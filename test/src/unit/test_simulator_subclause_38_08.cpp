#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

int SampleCbRtn(s_cb_data*) { return 0; }

class VpiGetCbInfoSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(VpiGetCbInfoSim, ReportsRegisteredCallbackInfo) {
  int marker = 0;
  VpiObject watched;
  watched.type = vpiReg;
  s_cb_data reg = {};
  reg.reason = cbValueChange;
  reg.cb_rtn = SampleCbRtn;
  reg.obj = VpiHandleOf(&watched);
  reg.index = 7;
  reg.user_data = reinterpret_cast<PLI_BYTE8*>(&marker);

  vpiHandle cb = vpi_register_cb(&reg);
  ASSERT_NE(cb, nullptr);

  s_cb_data out = {};
  vpi_get_cb_info(cb, &out);

  EXPECT_EQ(out.reason, cbValueChange);
  EXPECT_EQ(out.cb_rtn, SampleCbRtn);
  EXPECT_EQ(out.index, 7);
  EXPECT_EQ(out.user_data, reinterpret_cast<PLI_BYTE8*>(&marker));
}

TEST_F(VpiGetCbInfoSim, ReportsTriggerObject) {
  sim_ctx_.CreateVariable("sig", 8);
  vpi_ctx_.Attach(sim_ctx_);
  vpiHandle obj = vpi_handle_by_name(VpiText("sig"), nullptr);
  ASSERT_NE(obj, nullptr);

  s_cb_data reg = {};
  reg.reason = cbForce;
  reg.cb_rtn = SampleCbRtn;
  reg.obj = obj;
  vpiHandle cb = vpi_register_cb(&reg);
  ASSERT_NE(cb, nullptr);

  s_cb_data out = {};
  vpi_get_cb_info(cb, &out);
  EXPECT_EQ(out.obj, obj);
  EXPECT_EQ(out.reason, cbForce);
}

TEST_F(VpiGetCbInfoSim, ReportsTimeAndValuePointers) {
  s_vpi_time cb_time = {};
  s_vpi_value cb_value = {};
  s_cb_data reg = {};
  reg.reason = cbAtEndOfSimTime;
  reg.cb_rtn = SampleCbRtn;
  reg.time = &cb_time;
  reg.value = &cb_value;
  vpiHandle cb = vpi_register_cb(&reg);
  ASSERT_NE(cb, nullptr);

  s_cb_data out = {};
  vpi_get_cb_info(cb, &out);
  EXPECT_EQ(out.time, &cb_time);
  EXPECT_EQ(out.value, &cb_value);
}

TEST_F(VpiGetCbInfoSim, NullDestinationIsSafeNoOp) {
  s_cb_data reg = {};
  reg.reason = cbStartOfReset;
  reg.cb_rtn = SampleCbRtn;
  vpiHandle cb = vpi_register_cb(&reg);
  ASSERT_NE(cb, nullptr);

  vpi_get_cb_info(cb, nullptr);
}

TEST_F(VpiGetCbInfoSim, NullHandleLeavesDestinationUntouched) {
  s_cb_data out = {};
  out.reason = 4242;
  vpi_get_cb_info(nullptr, &out);
  EXPECT_EQ(out.reason, 4242);
}

TEST_F(VpiGetCbInfoSim, SystfCallbackHandleLeavesDestinationUntouched) {
  s_vpi_systf_data systf = {};
  systf.type = kVpiSysTask;
  systf.tfname = VpiText("$mytask");
  vpiHandle systf_cb = vpi_register_systf(&systf);
  ASSERT_NE(systf_cb, nullptr);

  s_cb_data out = {};
  out.reason = 5151;
  vpi_get_cb_info(systf_cb, &out);
  EXPECT_EQ(out.reason, 5151);
}

TEST_F(VpiGetCbInfoSim, NonCallbackHandleLeavesDestinationUntouched) {
  sim_ctx_.CreateVariable("v", 8);
  vpi_ctx_.Attach(sim_ctx_);
  vpiHandle var = vpi_handle_by_name(VpiText("v"), nullptr);
  ASSERT_NE(var, nullptr);

  s_cb_data out = {};
  out.reason = 3131;
  vpi_get_cb_info(var, &out);
  EXPECT_EQ(out.reason, 3131);
}

TEST_F(VpiGetCbInfoSim, ReportsTheRegistrationAfterTheCallbackHasFired) {
  s_vpi_time cb_time = {};
  cb_time.type = vpiSimTime;
  cb_time.low = 15;

  int marker = 0;
  s_cb_data reg = {};
  reg.reason = cbAfterDelay;
  reg.cb_rtn = SampleCbRtn;
  reg.time = &cb_time;
  reg.user_data = reinterpret_cast<PLI_BYTE8*>(&marker);
  vpiHandle cb = vpi_register_cb(&reg);
  ASSERT_NE(cb, nullptr);

  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbAfterDelay), 1);

  s_cb_data out = {};
  vpi_get_cb_info(cb, &out);
  EXPECT_EQ(out.reason, cbAfterDelay);
  EXPECT_EQ(out.time, &cb_time);
  EXPECT_EQ(out.user_data, reinterpret_cast<PLI_BYTE8*>(&marker));
  EXPECT_EQ(cb_time.low, 15u);
}

TEST_F(VpiGetCbInfoSim, AnAssertionCallbackHasNoSimulationRecordToReport) {
  VpiHandle placed = vpi_ctx_.CreateAssertionCallbackObject(7);
  s_cb_data out = {};
  out.reason = cbAtEndOfSimTime;
  vpi_get_cb_info(VpiHandleOf(placed), &out);
  EXPECT_EQ(out.reason, cbAtEndOfSimTime);
}

}  // namespace
}  // namespace delta
