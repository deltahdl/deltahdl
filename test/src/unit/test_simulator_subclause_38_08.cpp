#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// A stand-in application callback routine. vpi_get_cb_info() reports the stored
// cb_rtn pointer; it is never invoked by these tests.
int SampleCbRtn(VpiCbData*) { return 0; }

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

// §38.8: vpi_get_cb_info() shall report the information about a simulation-
// related callback into an s_cb_data structure.
TEST_F(VpiGetCbInfoSim, ReportsRegisteredCallbackInfo) {
  int marker = 0;
  s_cb_data reg = {};
  reg.reason = cbValueChange;
  reg.cb_rtn = SampleCbRtn;
  reg.index = 7;
  reg.user_data = &marker;

  vpiHandle cb = vpi_register_cb(&reg);
  ASSERT_NE(cb, nullptr);

  s_cb_data out = {};
  vpi_get_cb_info(cb, &out);

  EXPECT_EQ(out.reason, cbValueChange);
  EXPECT_EQ(out.cb_rtn, SampleCbRtn);
  EXPECT_EQ(out.index, 7);
  EXPECT_EQ(out.user_data, &marker);
}

// §38.8: the routine reports the callback's trigger object as well, so a handle
// stored at registration round-trips back through vpi_get_cb_info().
TEST_F(VpiGetCbInfoSim, ReportsTriggerObject) {
  sim_ctx_.CreateVariable("sig", 8);
  vpi_ctx_.Attach(sim_ctx_);
  vpiHandle obj = vpi_handle_by_name("sig", nullptr);
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

// §38.8: the reported s_cb_data carries the callback's time and value pointers
// too (Figure 38-2 fields), so they round-trip back through vpi_get_cb_info().
TEST_F(VpiGetCbInfoSim, ReportsTimeAndValuePointers) {
  VpiTime cb_time = {};
  VpiValue cb_value = {};
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

// §38.8: the memory for the destination structure is allocated by the
// application. The routine only writes the caller-supplied storage; it neither
// allocates nor frees it. A null destination is therefore a safe no-op.
TEST_F(VpiGetCbInfoSim, NullDestinationIsSafeNoOp) {
  s_cb_data reg = {};
  reg.reason = cbStartOfReset;
  reg.cb_rtn = SampleCbRtn;
  vpiHandle cb = vpi_register_cb(&reg);
  ASSERT_NE(cb, nullptr);

  vpi_get_cb_info(cb, nullptr);  // no crash, nothing to write into
}

// §38.8: a null handle names no callback, so the destination is left untouched.
TEST_F(VpiGetCbInfoSim, NullHandleLeavesDestinationUntouched) {
  s_cb_data out = {};
  out.reason = 4242;
  vpi_get_cb_info(nullptr, &out);
  EXPECT_EQ(out.reason, 4242);
}

// §38.8: vpi_get_cb_info() reports simulation-related callbacks only. A handle
// that names a system task/function callback (read through vpi_get_systf_info)
// is not a valid argument here, so the destination is left untouched.
TEST_F(VpiGetCbInfoSim, SystfCallbackHandleLeavesDestinationUntouched) {
  s_vpi_systf_data systf = {};
  systf.type = kVpiSysTask;
  systf.tfname = "$mytask";
  vpiHandle systf_cb = vpi_register_systf(&systf);
  ASSERT_NE(systf_cb, nullptr);

  s_cb_data out = {};
  out.reason = 5151;
  vpi_get_cb_info(systf_cb, &out);
  EXPECT_EQ(out.reason, 5151);
}

// §38.8: the handle names a callback. An object of any other kind names none,
// so the destination is left untouched rather than read out of the callback
// registry by whatever index that object happens to carry.
TEST_F(VpiGetCbInfoSim, NonCallbackHandleLeavesDestinationUntouched) {
  sim_ctx_.CreateVariable("v", 8);
  vpi_ctx_.Attach(sim_ctx_);
  vpiHandle var = vpi_handle_by_name("v", nullptr);
  ASSERT_NE(var, nullptr);

  s_cb_data out = {};
  out.reason = 3131;
  vpi_get_cb_info(var, &out);
  EXPECT_EQ(out.reason, 3131);
}

// §38.8 reports the registration, which a firing does not consume. §38.36.2
// hands a simulation-time callback's routine a structure of the run's own
// carrying the current simulation time, so what the application asked for is
// still there to be read back afterwards - the same time pointer, with the
// delay it was written with.
TEST_F(VpiGetCbInfoSim, ReportsTheRegistrationAfterTheCallbackHasFired) {
  VpiTime cb_time = {};
  cb_time.type = vpiSimTime;
  cb_time.low = 15;  // the delay asked for

  int marker = 0;
  s_cb_data reg = {};
  reg.reason = cbAfterDelay;
  reg.cb_rtn = SampleCbRtn;
  reg.time = &cb_time;
  reg.user_data = &marker;
  vpiHandle cb = vpi_register_cb(&reg);
  ASSERT_NE(cb, nullptr);

  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbAfterDelay), 1);

  s_cb_data out = {};
  vpi_get_cb_info(cb, &out);
  EXPECT_EQ(out.reason, cbAfterDelay);
  EXPECT_EQ(out.time, &cb_time);
  EXPECT_EQ(out.user_data, &marker);
  EXPECT_EQ(cb_time.low, 15u);
}

}  // namespace
}  // namespace delta
