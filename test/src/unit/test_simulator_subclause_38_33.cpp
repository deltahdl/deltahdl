#include <gtest/gtest.h>

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

VpiHandle g_restored_call = nullptr;
int g_restored_value = 0;
bool g_restore_ran = false;
int RestoreUserData(s_cb_data*) {
  g_restore_ran = true;
  vpi_put_userdata(VpiHandleOf(g_restored_call), &g_restored_value);
  return 0;
}

class VpiPutUserDataSim : public ::testing::Test {
 protected:
  void SetUp() override {
    g_restored_call = nullptr;
    g_restore_ran = false;
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

TEST_F(VpiPutUserDataSim, AssociatesUserDataWithFunctionCall) {
  VpiHandle call = MakeCall(vpiSysFuncCall);
  int marker = 0;

  EXPECT_EQ(vpi_put_userdata(VpiHandleOf(call), &marker), 1);
  EXPECT_EQ(vpi_get_userdata(VpiHandleOf(call)), &marker);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

TEST_F(VpiPutUserDataSim, NullUserDataValueStillSucceeds) {
  VpiHandle call = MakeCall(vpiSysFuncCall);

  EXPECT_EQ(vpi_put_userdata(VpiHandleOf(call), nullptr), 1);
  EXPECT_EQ(vpi_get_userdata(VpiHandleOf(call)), nullptr);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

TEST_F(VpiPutUserDataSim, NullHandleIsAnError) {
  int marker = 0;

  EXPECT_EQ(vpi_put_userdata(nullptr, &marker), 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

TEST_F(VpiPutUserDataSim, NonCallHandleIsRejected) {
  VpiHandle module = MakeCall(kVpiModule);
  int marker = 0;

  EXPECT_EQ(vpi_put_userdata(VpiHandleOf(module), &marker), 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
  EXPECT_EQ(vpi_get_userdata(VpiHandleOf(module)), nullptr);
}

TEST_F(VpiPutUserDataSim, RestartClearsUserData) {
  VpiHandle call = MakeCall(vpiSysFuncCall);
  int marker = 0;
  ASSERT_EQ(vpi_put_userdata(VpiHandleOf(call), &marker), 1);
  ASSERT_EQ(vpi_get_userdata(VpiHandleOf(call)), &marker);

  vpi_ctx_.DispatchRestart();

  EXPECT_EQ(vpi_get_userdata(VpiHandleOf(call)), nullptr);
}

TEST_F(VpiPutUserDataSim, ResetClearsUserData) {
  VpiHandle call = MakeCall(vpiSysTaskCall);
  int marker = 0;
  ASSERT_EQ(vpi_put_userdata(VpiHandleOf(call), &marker), 1);
  ASSERT_EQ(vpi_get_userdata(VpiHandleOf(call)), &marker);

  vpi_ctx_.DispatchReset();

  EXPECT_EQ(vpi_get_userdata(VpiHandleOf(call)), nullptr);
}

TEST_F(VpiPutUserDataSim, TheFieldCanBeSetUpAgainFromAnEndOfRestartCallback) {
  VpiHandle call = MakeCall(vpiSysTaskCall);
  int before_restart = 0;
  ASSERT_EQ(vpi_put_userdata(VpiHandleOf(call), &before_restart), 1);

  g_restored_call = call;
  s_cb_data cb = {};
  cb.reason = cbEndOfRestart;
  cb.cb_rtn = RestoreUserData;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  vpi_ctx_.DispatchRestart();

  ASSERT_TRUE(g_restore_ran);
  EXPECT_EQ(vpi_get_userdata(VpiHandleOf(call)), &g_restored_value);
  EXPECT_NE(vpi_get_userdata(VpiHandleOf(call)), &before_restart);
}

using UserDataOfABuiltInCall = VpiDesignRun;

TEST_F(UserDataOfABuiltInCall, PuttingItIsAnError) {
  Run("module top;\n"
      "  initial $display(\"x\");\n"
      "endmodule\n");
  std::vector<vpiHandle> processes = ObjectsOf(vpiProcess, By("top"));
  ASSERT_EQ(processes.size(), 1u);
  vpiHandle display = vpi_handle(vpiStmt, processes[0]);
  ASSERT_NE(display, nullptr);
  ASSERT_EQ(vpi_get(vpiType, display), vpiSysTaskCall);
  int value = 1;
  EXPECT_EQ(vpi_put_userdata(display, &value), 0);
  EXPECT_NE(vpi_chk_error(nullptr), 0);
  EXPECT_EQ(vpi_get_userdata(display), nullptr);
}

TEST_F(UserDataOfABuiltInCall, PuttingItOnAFunctionCallIsAnError) {
  Run("module top; longint x;\n"
      "  initial x = $time;\n"
      "endmodule\n");
  vpiHandle initial = ObjectsOf(vpiProcess, By("top")).at(0);
  vpiHandle time = vpi_handle(vpiRhs, vpi_handle(vpiStmt, initial));
  ASSERT_NE(time, nullptr);
  ASSERT_EQ(vpi_get(vpiType, time), vpiSysFuncCall);
  int value = 1;
  EXPECT_EQ(vpi_put_userdata(time, &value), 0);
  const PLI_INT32 kPutError = vpi_chk_error(nullptr);
  EXPECT_EQ(kPutError, vpiError);
  EXPECT_EQ(vpi_get_userdata(time), nullptr);
}

std::vector<void*> held_by_calls;
std::vector<PLI_INT32> put_results;
int call_slots[2] = {};
int next_call_slot = 0;

PLI_INT32 TagCalltf(PLI_BYTE8*) {
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  void* held = vpi_get_userdata(call);
  held_by_calls.push_back(held);
  if (held == nullptr && next_call_slot < 2) {
    put_results.push_back(
        vpi_put_userdata(call, &call_slots[next_call_slot++]));
  }
  return 0;
}

class UserDataOfEachCall : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    held_by_calls.clear();
    put_results.clear();
    next_call_slot = 0;
    s_vpi_systf_data task = {};
    task.type = vpiSysTask;
    task.tfname = VpiText("$tag");
    task.calltf = &TagCalltf;
    ASSERT_NE(vpi_register_systf(&task), nullptr);
  }
};

TEST_F(UserDataOfEachCall, TwoCallsOfOneTaskInOneScopeKeepTheirOwn) {
  Run("module top;\n"
      "  initial repeat (2) begin $tag; $tag; end\n"
      "endmodule\n");
  EXPECT_EQ(put_results, (std::vector<PLI_INT32>{1, 1}));
  EXPECT_EQ(held_by_calls, (std::vector<void*>{nullptr, nullptr, &call_slots[0],
                                               &call_slots[1]}));
}

}  // namespace
}  // namespace delta
