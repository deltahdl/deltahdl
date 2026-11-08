#include <gtest/gtest.h>

#include <algorithm>
#include <deque>
#include <vector>

#include "common/arena.h"
#include "fixture_vpi_run.h"
#include "simulator/scheduler.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

VpiHandle g_reset_call = nullptr;
void* g_seen_during_reset = nullptr;
int g_value_set_during_reset = 0;
bool g_reset_routine_ran = false;
int ReadAndRestoreUserData(s_cb_data*) {
  g_reset_routine_ran = true;
  g_seen_during_reset = vpi_get_userdata(VpiHandleOf(g_reset_call));
  vpi_put_userdata(VpiHandleOf(g_reset_call), &g_value_set_during_reset);
  return 0;
}

class VpiGetUserDataSim : public ::testing::Test {
 protected:
  void SetUp() override {
    g_reset_call = nullptr;
    g_seen_during_reset = nullptr;
    g_reset_routine_ran = false;
    vpi_ctx_.SetScheduler(&scheduler_);
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiHandle MakeCall(int type) {
    VpiHandle obj = vpi_ctx_.CreateModule("c", "c");
    obj->type = type;
    obj->user_defined = true;
    return obj;
  }

  Arena arena_;
  Scheduler scheduler_{arena_};
  VpiContext vpi_ctx_;
};

TEST_F(VpiGetUserDataSim, ReturnsValueAssociatedByPut) {
  VpiHandle call = MakeCall(vpiSysFuncCall);
  int marker = 0;
  ASSERT_EQ(vpi_put_userdata(VpiHandleOf(call), &marker), 1);

  EXPECT_EQ(vpi_get_userdata(VpiHandleOf(call)), &marker);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

TEST_F(VpiGetUserDataSim, ReturnsNullWhenNothingAssociated) {
  VpiHandle call = MakeCall(vpiSysTaskCall);

  EXPECT_EQ(vpi_get_userdata(VpiHandleOf(call)), nullptr);
}

TEST_F(VpiGetUserDataSim, ReturnsNullForNullHandle) {
  EXPECT_EQ(vpi_get_userdata(nullptr), nullptr);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

TEST_F(VpiGetUserDataSim, ReturnsNullForNonCallHandle) {
  VpiHandle module = MakeCall(kVpiModule);

  EXPECT_EQ(vpi_get_userdata(VpiHandleOf(module)), nullptr);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

TEST_F(VpiGetUserDataSim, ReturnsNullAfterRestart) {
  VpiHandle call = MakeCall(vpiSysFuncCall);
  int marker = 0;
  ASSERT_EQ(vpi_put_userdata(VpiHandleOf(call), &marker), 1);
  ASSERT_EQ(vpi_get_userdata(VpiHandleOf(call)), &marker);

  vpi_ctx_.DispatchRestart();

  EXPECT_EQ(vpi_get_userdata(VpiHandleOf(call)), nullptr);
}

TEST_F(VpiGetUserDataSim, ReturnsNullAfterReset) {
  VpiHandle call = MakeCall(vpiSysFuncCall);
  int marker = 0;
  ASSERT_EQ(vpi_put_userdata(VpiHandleOf(call), &marker), 1);
  ASSERT_EQ(vpi_get_userdata(VpiHandleOf(call)), &marker);

  vpi_ctx_.DispatchReset();

  EXPECT_EQ(vpi_get_userdata(VpiHandleOf(call)), nullptr);
}

TEST_F(VpiGetUserDataSim, AReadDuringEndOfResetStartsFromNullAndCanBeSetAgain) {
  VpiHandle call = MakeCall(vpiSysTaskCall);
  int before_reset = 0;
  ASSERT_EQ(vpi_put_userdata(VpiHandleOf(call), &before_reset), 1);

  g_reset_call = call;
  s_cb_data cb = {};
  cb.reason = cbEndOfReset;
  cb.cb_rtn = ReadAndRestoreUserData;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  vpi_ctx_.DispatchReset();

  ASSERT_TRUE(g_reset_routine_ran);
  EXPECT_EQ(g_seen_during_reset, nullptr);
  EXPECT_EQ(vpi_get_userdata(VpiHandleOf(call)), &g_value_set_during_reset);
  EXPECT_NE(vpi_get_userdata(VpiHandleOf(call)), &before_reset);
}

std::vector<int> counts_read;

std::deque<int>& CallCounts() {
  static std::deque<int> counts;
  return counts;
}

PLI_INT32 CountCalltf(PLI_BYTE8*) {
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  auto* count = static_cast<int*>(vpi_get_userdata(call));
  if (count == nullptr) count = &CallCounts().emplace_back(0);
  ++*count;
  counts_read.push_back(*count);
  vpi_put_userdata(call, count);
  return 0;
}

class UserDataOfACallInATask : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    counts_read.clear();
    CallCounts().clear();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$count");
    data.calltf = &CountCalltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }
};

TEST_F(UserDataOfACallInATask, ItLastsFromOneInvocationToTheNext) {
  Run("module top;\n"
      "  task t; $count; endtask\n"
      "  initial begin t; t; end\n"
      "endmodule\n");
  EXPECT_EQ(counts_read, (std::vector<int>{1, 2}));
}

TEST_F(UserDataOfACallInATask, EachInstanceOfItsModuleHasItsOwn) {
  Run("module child;\n"
      "  task t; $count; endtask\n"
      "  initial begin t; t; end\n"
      "endmodule\n"
      "module top; child a(); child b(); endmodule\n");
  std::vector<int> counts = counts_read;
  std::ranges::sort(counts);
  EXPECT_EQ(counts, (std::vector<int>{1, 1, 2, 2}));
}

}  // namespace
}  // namespace delta
