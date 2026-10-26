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

// §38.4: vpiFinish requests $finish on return of the application routine and
// carries the diagnostic message level that task reports; vpi_control() returns
// 1 on success and forwards the level through to the pending built-in.
TEST_F(VpiSimControlSim, ControlFinishCarriesDiagLevel) {
  EXPECT_FALSE(vpi_ctx_.FinishRequested());
  int result = vpi_control(vpiFinish, 2);
  EXPECT_EQ(result, 1);
  EXPECT_TRUE(vpi_ctx_.FinishRequested());
  EXPECT_EQ(vpi_ctx_.FinishDiagLevel(), 2);
}

// §38.4: vpiStop likewise requests $stop and carries its diagnostic message
// level.
TEST_F(VpiSimControlSim, ControlStopCarriesDiagLevel) {
  EXPECT_FALSE(vpi_ctx_.StopRequested());
  int result = vpi_control(vpiStop, 1);
  EXPECT_EQ(result, 1);
  EXPECT_TRUE(vpi_ctx_.StopRequested());
  EXPECT_EQ(vpi_ctx_.StopDiagLevel(), 1);
}

// §38.4: vpiReset asks for $reset, which this implementation is without, as
// Annex D.1 allows, so the request fails, and neither a stop nor a finish is
// requested in its place.
TEST_F(VpiSimControlSim, ControlResetFails) {
  EXPECT_EQ(vpi_control(vpiReset, 4, 5, 6), 0);
  EXPECT_FALSE(vpi_ctx_.StopRequested());
  EXPECT_FALSE(vpi_ctx_.FinishRequested());
}

// §38.4: vpiSetInteractiveScope immediately switches the tool's interactive
// scope to the supplied vpiScope handle, and retargets to a *new* scope each
// time it is invoked, so a later call replaces the scope an earlier call
// established rather than being ignored once a scope is set. This subsumes the
// base case, setting the scope for the first time, in its first retarget.
TEST_F(VpiSimControlSim, ControlSetInteractiveScopeReplacesPriorScope) {
  EXPECT_EQ(vpi_ctx_.InteractiveScope(), nullptr);
  VpiHandle first = vpi_ctx_.CreateModule("top", "top");
  EXPECT_EQ(vpi_control(vpiSetInteractiveScope, first), 1);
  EXPECT_EQ(vpi_ctx_.InteractiveScope(), first);

  VpiHandle second = vpi_ctx_.CreateModule("sub", "top.sub");
  EXPECT_EQ(vpi_control(vpiSetInteractiveScope, second), 1);
  EXPECT_EQ(vpi_ctx_.InteractiveScope(), second);
}

// §38.4: vpiSetInteractiveScope takes a handle of an object of the vpiScope
// class (§37.12). A null handle, or one naming a net, names no scope to change
// to, so the call fails and the scope stays where it was (#7454).
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

// §38.4: an operation vpi_control() does not recognize fails (returns 0) and
// does nothing else: no stop or finish is requested and the interactive scope
// is left as it was.
TEST_F(VpiSimControlSim, ControlUnknownOpIsInert) {
  int result = vpi_control(12345, 0);
  EXPECT_EQ(result, 0);
  EXPECT_FALSE(vpi_ctx_.StopRequested());
  EXPECT_FALSE(vpi_ctx_.FinishRequested());
  EXPECT_EQ(vpi_ctx_.InteractiveScope(), nullptr);
}

PLI_INT32 FinishCalltf(PLI_BYTE8* /*user_data*/) {
  vpi_control(vpiFinish, 0);
  return 0;
}

PLI_INT32 StopCalltf(PLI_BYTE8* /*user_data*/) {
  vpi_control(vpiStop, 0);
  return 0;
}

class FinishOfARun : public VpiDesignRun {
 protected:
  // Runs a design whose `$probe` at time 5 calls `calltf` and which writes
  // `top.after` at time 10; answers what `top.after` holds once it ends.
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

// §38.4: vpi_control(vpiFinish) ends the run as $finish does once the
// application routine returns, so an event the design scheduled for later
// never runs (#5105).
TEST_F(FinishOfARun, AFinishFromACalltfEndsTheRun) {
  EXPECT_EQ(AfterOnceProbedBy(&FinishCalltf), 0);
}

// §38.4: vpi_control(vpiStop) suspends the run as $stop does once the
// application routine returns, a run with no interactive phase to resume
// ending there (#5134).
TEST_F(FinishOfARun, AStopFromACalltfStopsTheRun) {
  EXPECT_EQ(AfterOnceProbedBy(&StopCalltf), 0);
}

// The run a calltf below looks at while it runs, and what it saw there.
SimContext* looked_at_run = nullptr;
bool finish_seen_in_routine = true;
int reset_callbacks = 0;
int reset_result = -1;

PLI_INT32 FinishThenLookCalltf(PLI_BYTE8* /*user_data*/) {
  vpi_control(vpiFinish, 0);
  finish_seen_in_routine = looked_at_run->FinishRequested();
  return 0;
}

PLI_INT32 CountResetCallback(p_cb_data /*data*/) {
  ++reset_callbacks;
  return 0;
}

PLI_INT32 ResetCalltf(PLI_BYTE8* /*user_data*/) {
  reset_result = vpi_control(vpiReset, 0, 0, 0);
  return 0;
}

// §38.4: vpiFinish has $finish execute on return of the application routine,
// not during the call: the routine goes on running with the run not yet
// finishing (#7452).
TEST_F(FinishOfARun, AFinishActsOnceTheRoutineReturns) {
  looked_at_run = &f_.ctx;
  EXPECT_EQ(AfterOnceProbedBy(&FinishThenLookCalltf), 0);
  EXPECT_FALSE(finish_seen_in_routine);
  EXPECT_TRUE(f_.ctx.FinishRequested());
}

// §38.4 with §38.36.3: a vpiReset from a calltf fails, as this implementation
// is without $reset, so no reset callback is called once the routine returns
// and the run goes on to the event it scheduled for later.
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

// §38.4: vpiSetInteractiveScope changes the interactive scope the tool's
// interactive tasks, $showscopes and $showvars among them, name objects from
// -- the one $scope sets (D.11) (#7453).
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
