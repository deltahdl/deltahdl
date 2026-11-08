#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_vpi_run.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiSimControlSim : public ::testing::Test {
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

TEST_F(VpiSimControlSim, ControlFinishCarriesDiagLevel) {
  EXPECT_FALSE(vpi_ctx_.FinishRequested());
  int result = vpi_control(vpiFinish, 2);
  EXPECT_EQ(result, 1);
  EXPECT_TRUE(vpi_ctx_.FinishRequested());
  EXPECT_EQ(vpi_ctx_.FinishDiagLevel(), 2);
}

TEST_F(VpiSimControlSim, ControlStopCarriesDiagLevel) {
  EXPECT_FALSE(vpi_ctx_.StopRequested());
  int result = vpi_control(vpiStop, 1);
  EXPECT_EQ(result, 1);
  EXPECT_TRUE(vpi_ctx_.StopRequested());
  EXPECT_EQ(vpi_ctx_.StopDiagLevel(), 1);
}

TEST_F(VpiSimControlSim, ControlResetFails) {
  EXPECT_EQ(vpi_control(vpiReset, 4, 5, 6), 0);
  EXPECT_FALSE(vpi_ctx_.StopRequested());
  EXPECT_FALSE(vpi_ctx_.FinishRequested());
}

TEST_F(VpiSimControlSim, ControlSetInteractiveScopeReplacesPriorScope) {
  EXPECT_EQ(vpi_ctx_.InteractiveScope(), nullptr);
  VpiHandle first = vpi_ctx_.CreateModule("top", "top");
  EXPECT_EQ(vpi_control(vpiSetInteractiveScope, first), 1);
  EXPECT_EQ(vpi_ctx_.InteractiveScope(), first);

  VpiHandle second = vpi_ctx_.CreateModule("sub", "top.sub");
  EXPECT_EQ(vpi_control(vpiSetInteractiveScope, second), 1);
  EXPECT_EQ(vpi_ctx_.InteractiveScope(), second);
}

TEST_F(VpiSimControlSim, ControlSetInteractiveScopeRefusesWhatIsNoScope) {
  VpiHandle top = vpi_ctx_.CreateModule("top", "top");
  ASSERT_EQ(vpi_control(vpiSetInteractiveScope, top), 1);
  VpiObject net;
  net.type = vpiNet;
  EXPECT_EQ(
      vpi_control(vpiSetInteractiveScope, static_cast<vpiHandle>(nullptr)), 0);
  EXPECT_EQ(vpi_control(vpiSetInteractiveScope, VpiHandleOf(&net)), 0);
  EXPECT_EQ(vpi_ctx_.InteractiveScope(), top);
}

TEST_F(VpiSimControlSim, ControlUnknownOpIsInert) {
  int result = vpi_control(12345, 0);
  EXPECT_EQ(result, 0);
  EXPECT_FALSE(vpi_ctx_.StopRequested());
  EXPECT_FALSE(vpi_ctx_.FinishRequested());
  EXPECT_EQ(vpi_ctx_.InteractiveScope(), nullptr);
}

PLI_INT32 FinishCalltf(PLI_BYTE8*) {
  vpi_control(vpiFinish, 0);
  return 0;
}

PLI_INT32 StopCalltf(PLI_BYTE8*) {
  vpi_control(vpiStop, 0);
  return 0;
}

class FinishOfARun : public VpiDesignRun {
 protected:
  int AfterOnceProbedBy(PLI_INT32 (*calltf)(PLI_BYTE8*)) {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$probe");
    data.calltf = calltf;
    EXPECT_NE(vpi_register_systf(&data), nullptr);
    Run("module top; int after = 0;\n"
        "  initial begin #5 $probe; #5 after = 1; end\n"
        "endmodule\n");
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(By("top.after"), &value);
    return value.value.integer;
  }
};

TEST_F(FinishOfARun, AFinishFromACalltfEndsTheRun) {
  EXPECT_EQ(AfterOnceProbedBy(&FinishCalltf), 0);
}

TEST_F(FinishOfARun, AStopFromACalltfStopsTheRun) {
  EXPECT_EQ(AfterOnceProbedBy(&StopCalltf), 0);
}

SimContext* looked_at_run = nullptr;
bool finish_seen_in_routine = true;
int reset_callbacks = 0;
int reset_result = -1;

PLI_INT32 FinishThenLookCalltf(PLI_BYTE8*) {
  vpi_control(vpiFinish, 0);
  finish_seen_in_routine = looked_at_run->FinishRequested();
  return 0;
}

PLI_INT32 CountResetCallback(p_cb_data) {
  ++reset_callbacks;
  return 0;
}

PLI_INT32 ResetCalltf(PLI_BYTE8*) {
  reset_result = vpi_control(vpiReset, 0, 0, 0);
  return 0;
}

TEST_F(FinishOfARun, AFinishActsOnceTheRoutineReturns) {
  looked_at_run = &f_.ctx;
  EXPECT_EQ(AfterOnceProbedBy(&FinishThenLookCalltf), 0);
  EXPECT_FALSE(finish_seen_in_routine);
  EXPECT_TRUE(f_.ctx.FinishRequested());
}

TEST_F(FinishOfARun, AResetFromACalltfFailsAndTheRunGoesOn) {
  reset_callbacks = 0;
  reset_result = -1;
  s_cb_data cb = {};
  cb.reason = cbEndOfReset;
  cb.cb_rtn = &CountResetCallback;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);
  EXPECT_EQ(AfterOnceProbedBy(&ResetCalltf), 1);
  EXPECT_EQ(reset_result, 0);
  EXPECT_EQ(reset_callbacks, 0);
}

TEST_F(FinishOfARun, SetInteractiveScopeChangesTheRunsScope) {
  Run("module sub; endmodule\n"
      "module top; sub u(); initial $noop; endmodule\n");
  vpiHandle u = By("top.u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(vpi_control(vpiSetInteractiveScope, u), 1);
  EXPECT_EQ(f_.ctx.InteractiveScope(), "top.u");
}

}  // namespace
}  // namespace delta
