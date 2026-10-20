#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <functional>
#include <iterator>
#include <string>
#include <vector>

#include "helpers_assertion_run.h"
#include "simulator/assertion_api.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

constexpr const char* kA = "top.a1";

// §39.5.2: the six per-assertion action-control constants must exist and be
// distinct from one another.
TEST(SvVpiUser, AssertionActionControlConstants) {
  int values[] = {
      vpiAssertionDisablePassAction,    vpiAssertionEnablePassAction,
      vpiAssertionDisableFailAction,    vpiAssertionEnableFailAction,
      vpiAssertionDisableVacuousAction, vpiAssertionEnableNonvacuousAction};
  for (size_t i = 0; i < std::size(values); ++i) {
    for (size_t j = i + 1; j < std::size(values); ++j) {
      EXPECT_NE(values[i], values[j]);
    }
  }
}

// §39.5.2 intro: only assertion statement handles (assert/assume/cover, and
// restrict, §16.14's fourth concurrent assertion statement) are valid;
// sequence and property instances are not.
TEST(AssertionControl, OnlyAssertionStatementHandlesValid) {
  EXPECT_TRUE(AssertionApi::IsAssertionStatementHandle(vpiAssert));
  EXPECT_TRUE(AssertionApi::IsAssertionStatementHandle(vpiAssume));
  EXPECT_TRUE(AssertionApi::IsAssertionStatementHandle(vpiCover));
  EXPECT_TRUE(AssertionApi::IsAssertionStatementHandle(vpiRestrict));
  EXPECT_TRUE(AssertionApi::IsAssertionStatementHandle(vpiImmediateAssert));

  EXPECT_FALSE(AssertionApi::IsAssertionStatementHandle(vpiSequenceInst));
  EXPECT_FALSE(AssertionApi::IsAssertionStatementHandle(vpiPropertyInst));
  EXPECT_FALSE(AssertionApi::IsAssertionStatementHandle(vpiSequenceDecl));
  EXPECT_FALSE(AssertionApi::IsAssertionStatementHandle(vpiProperty));
  EXPECT_FALSE(AssertionApi::IsAssertionStatementHandle(vpiPropertyDecl));
}

// §39.5.2 intro: an assertion statement in immediate form is equally a valid
// target. The assume and cover statements each have an immediate flavor, which
// are distinct handle types and must both be accepted alongside the concurrent
// forms and the immediate assert already covered above.
TEST(AssertionControl, ImmediateAssumeAndCoverHandlesValid) {
  EXPECT_TRUE(AssertionApi::IsAssertionStatementHandle(vpiImmediateAssume));
  EXPECT_TRUE(AssertionApi::IsAssertionStatementHandle(vpiImmediateCover));
}

// §39.5.2 intro: the second argument shall be a valid assertion handle; an
// empty (invalid) handle is rejected.
TEST(AssertionControl, EmptyHandleRejected) {
  AssertionApi api;
  EXPECT_FALSE(api.Control(vpiAssertionDisable, {}));
  EXPECT_FALSE(api.ControlAttempt(vpiAssertionKill, {}, 10));
  EXPECT_FALSE(
      api.ControlStep(vpiAssertionEnableStep, {}, 10, vpiAssertionClockSteps));
}

// §39.5.2 vpiAssertionReset: discards attempts in progress for this assertion
// and resets it to its initial state.
TEST(AssertionControl, ResetDiscardsAttemptsAndRestoresInitialState) {
  AssertionApi api;
  api.NoteAssertionAttemptStarted(kA, 10);
  api.NoteAssertionAttemptStarted(kA, 20);
  api.Control(vpiAssertionDisable, kA);
  api.Control(vpiAssertionDisableFailAction, kA);

  EXPECT_TRUE(api.Control(vpiAssertionReset, kA));

  EXPECT_EQ(api.AssertionAttemptsInProgress(kA), 0u);
  EXPECT_TRUE(api.AssertionEnabled(kA));
  EXPECT_TRUE(api.AssertionFailActionEnabled(kA));
  EXPECT_TRUE(api.AssertionPassActionEnabled(kA));
  EXPECT_FALSE(api.AssertionStepEnabled(kA, 10));
}

// §39.5.2 vpiAssertionLock / vpiAssertionUnlock: while locked, status cannot be
// changed without first unlocking.
TEST(AssertionControl, LockBlocksChangesUntilUnlocked) {
  AssertionApi api;
  EXPECT_TRUE(api.Control(vpiAssertionLock, kA));
  EXPECT_TRUE(api.AssertionLocked(kA));

  // A change while locked is rejected and has no effect.
  EXPECT_FALSE(api.Control(vpiAssertionDisable, kA));
  EXPECT_TRUE(api.AssertionEnabled(kA));

  // Unlock is permitted even while locked.
  EXPECT_TRUE(api.Control(vpiAssertionUnlock, kA));
  EXPECT_FALSE(api.AssertionLocked(kA));
  EXPECT_TRUE(api.Control(vpiAssertionDisable, kA));
  EXPECT_FALSE(api.AssertionEnabled(kA));
}

// §39.5.2 vpiAssertionDisable: disables starting of new attempts; existing
// attempts are unaffected. vpiAssertionEnable re-enables.
TEST(AssertionControl, DisableLeavesExistingAttemptsEnableRestores) {
  AssertionApi api;
  api.NoteAssertionAttemptStarted(kA, 10);

  EXPECT_TRUE(api.Control(vpiAssertionDisable, kA));
  EXPECT_FALSE(api.AssertionEnabled(kA));
  EXPECT_EQ(api.AssertionAttemptsInProgress(kA), 1u);

  EXPECT_TRUE(api.Control(vpiAssertionEnable, kA));
  EXPECT_TRUE(api.AssertionEnabled(kA));
}

// §39.5.2 vpiAssertionDisablePassAction / EnablePassAction: pass action covers
// both vacuous and nonvacuous success.
TEST(AssertionControl, PassActionTogglesVacuousAndNonvacuous) {
  AssertionApi api;
  EXPECT_TRUE(api.Control(vpiAssertionDisablePassAction, kA));
  EXPECT_FALSE(api.AssertionPassActionEnabled(kA));
  EXPECT_FALSE(api.AssertionVacuousActionEnabled(kA));
  EXPECT_FALSE(api.AssertionNonvacuousActionEnabled(kA));

  EXPECT_TRUE(api.Control(vpiAssertionEnablePassAction, kA));
  EXPECT_TRUE(api.AssertionPassActionEnabled(kA));
  EXPECT_TRUE(api.AssertionVacuousActionEnabled(kA));
  EXPECT_TRUE(api.AssertionNonvacuousActionEnabled(kA));
}

// §39.5.2 vpiAssertionDisableFailAction / EnableFailAction.
TEST(AssertionControl, FailActionToggles) {
  AssertionApi api;
  EXPECT_TRUE(api.Control(vpiAssertionDisableFailAction, kA));
  EXPECT_FALSE(api.AssertionFailActionEnabled(kA));
  EXPECT_TRUE(api.Control(vpiAssertionEnableFailAction, kA));
  EXPECT_TRUE(api.AssertionFailActionEnabled(kA));
}

// §39.5.2 vpiAssertionDisableVacuousAction / EnableNonvacuousAction: the
// vacuous and nonvacuous pass actions are controlled independently.
TEST(AssertionControl, VacuousAndNonvacuousControlledIndependently) {
  AssertionApi api;
  EXPECT_TRUE(api.Control(vpiAssertionDisableVacuousAction, kA));
  EXPECT_FALSE(api.AssertionVacuousActionEnabled(kA));
  EXPECT_TRUE(api.AssertionNonvacuousActionEnabled(kA));

  api.Control(vpiAssertionDisablePassAction, kA);
  EXPECT_TRUE(api.Control(vpiAssertionEnableNonvacuousAction, kA));
  EXPECT_TRUE(api.AssertionNonvacuousActionEnabled(kA));
  EXPECT_FALSE(api.AssertionVacuousActionEnabled(kA));
}

// §39.5.2 vpiAssertionKill: discards the given attempt (identified by its start
// time) but leaves the assertion enabled and does not reset its state. Other
// attempts in progress are untouched.
TEST(AssertionControl, KillDiscardsGivenAttemptKeepsAssertionEnabled) {
  AssertionApi api;
  api.NoteAssertionAttemptStarted(kA, 10);
  api.NoteAssertionAttemptStarted(kA, 20);

  EXPECT_TRUE(
      api.ControlAttempt(vpiAssertionKill, kA, /*attempt_start_time=*/10));

  EXPECT_EQ(api.AssertionAttemptsInProgress(kA), 1u);
  EXPECT_TRUE(api.AssertionEnabled(kA));
  // Only the given attempt was discarded; the one started at time 20 remains
  // and can itself be killed, dropping the count to zero.
  EXPECT_TRUE(
      api.ControlAttempt(vpiAssertionKill, kA, /*attempt_start_time=*/20));
  EXPECT_EQ(api.AssertionAttemptsInProgress(kA), 0u);
}

// §39.5.2 vpiAssertionKill: it discards the given attempt but leaves the
// assertion enabled and does not reset any state used by this assertion. Unlike
// vpiAssertionReset, a kill from a non-default state (disabled, with a disabled
// fail action) must preserve that state rather than restoring the defaults.
TEST(AssertionControl, KillPreservesAssertionStateUnlikeReset) {
  AssertionApi api;
  api.NoteAssertionAttemptStarted(kA, 10);
  api.NoteAssertionAttemptStarted(kA, 20);
  // Drive the assertion into a non-default control state.
  api.Control(vpiAssertionDisable, kA);
  api.Control(vpiAssertionDisableFailAction, kA);

  EXPECT_TRUE(
      api.ControlAttempt(vpiAssertionKill, kA, /*attempt_start_time=*/10));

  // The named attempt is gone, but every other piece of state is untouched:
  // the assertion stays disabled and its fail action stays disabled.
  EXPECT_EQ(api.AssertionAttemptsInProgress(kA), 1u);
  EXPECT_FALSE(api.AssertionEnabled(kA));
  EXPECT_FALSE(api.AssertionFailActionEnabled(kA));
}

// §39.5.2 vpiAssertionEnableStep: the stepping mode of an attempt cannot be
// modified once the attempt has started; a later enable is accepted but has no
// effect. Stepping enabled before the attempt starts does take effect and
// persists once it starts.
TEST(AssertionControl, StepModeFrozenAfterAttemptStarts) {
  AssertionApi api;
  api.NoteAssertionAttemptStarted(kA, 40);
  EXPECT_TRUE(api.ControlStep(vpiAssertionEnableStep, kA,
                              /*attempt_start_time=*/40,
                              vpiAssertionClockSteps));
  EXPECT_FALSE(api.AssertionStepEnabled(kA, 40));  // no effect after start

  EXPECT_TRUE(api.ControlStep(vpiAssertionEnableStep, kA,
                              /*attempt_start_time=*/50,
                              vpiAssertionClockSteps));
  EXPECT_TRUE(api.AssertionStepEnabled(kA, 50));  // set before the attempt
  api.NoteAssertionAttemptStarted(kA, 50);
  EXPECT_TRUE(api.AssertionStepEnabled(kA, 50));  // persists once started
}

// §39.5.2 vpiAssertionDisableStep: disables step callbacks; no effect when
// stepping is not enabled (idempotent).
TEST(AssertionControl, DisableStepClearsStepping) {
  AssertionApi api;
  api.ControlStep(vpiAssertionEnableStep, kA, /*attempt_start_time=*/30,
                  vpiAssertionClockSteps);
  ASSERT_TRUE(api.AssertionStepEnabled(kA, 30));

  EXPECT_TRUE(api.ControlAttempt(vpiAssertionDisableStep, kA,
                                 /*attempt_start_time=*/30));
  EXPECT_FALSE(api.AssertionStepEnabled(kA, 30));

  // Idempotent when already disabled.
  EXPECT_TRUE(api.ControlAttempt(vpiAssertionDisableStep, kA,
                                 /*attempt_start_time=*/30));
  EXPECT_FALSE(api.AssertionStepEnabled(kA, 30));
}

// §39.5.2 vpiAssertionEnableStep: enables step callbacks for the given attempt;
// stepping is disabled by default.
TEST(AssertionControl, EnableStepEnablesStepping) {
  AssertionApi api;
  EXPECT_FALSE(api.AssertionStepEnabled(kA, 30));  // disabled by default
  EXPECT_TRUE(api.ControlStep(vpiAssertionEnableStep, kA,
                              /*attempt_start_time=*/30,
                              vpiAssertionClockSteps));
  EXPECT_TRUE(api.AssertionStepEnabled(kA, 30));
}

// §39.5.2 vpiAssertionClockSteps: the fourth argument shall be a valid step
// control constant; any other value rejects the control.
TEST(AssertionControl, EnableStepRequiresStepControlConstant) {
  AssertionApi api;
  EXPECT_FALSE(
      api.ControlStep(vpiAssertionEnableStep, kA, /*attempt_start_time=*/30,
                      /*not a step control constant=*/vpiAssertionEnable));
  EXPECT_FALSE(api.AssertionStepEnabled(kA, 30));

  EXPECT_TRUE(api.ControlStep(vpiAssertionEnableStep, kA,
                              /*attempt_start_time=*/30,
                              vpiAssertionClockSteps));
  EXPECT_TRUE(api.AssertionStepEnabled(kA, 30));
}

// §39.5.2: per-assertion controls are scoped to the named assertion and do not
// affect other assertions.
TEST(AssertionControl, ControlsAreScopedPerAssertion) {
  AssertionApi api;
  EXPECT_TRUE(api.Control(vpiAssertionDisable, kA));
  EXPECT_FALSE(api.AssertionEnabled(kA));
  EXPECT_TRUE(api.AssertionEnabled("top.a2"));
}

// §39.5.2 vpiAssertionDisable / vpiAssertionEnable: repeating a control has no
// effect when the assertion is already in the requested state (idempotent), and
// the control is still reported as applied.
TEST(AssertionControl, EnableDisableAreIdempotent) {
  AssertionApi api;
  // Enabling an already-enabled assertion has no effect.
  EXPECT_TRUE(api.Control(vpiAssertionEnable, kA));
  EXPECT_TRUE(api.AssertionEnabled(kA));

  EXPECT_TRUE(api.Control(vpiAssertionDisable, kA));
  // Disabling again leaves it disabled.
  EXPECT_TRUE(api.Control(vpiAssertionDisable, kA));
  EXPECT_FALSE(api.AssertionEnabled(kA));
}

// §39.5.2 action controls: repeating a pass/fail/vacuous action control when it
// is already in the requested state has no effect.
TEST(AssertionControl, ActionControlsAreIdempotent) {
  AssertionApi api;
  EXPECT_TRUE(api.Control(vpiAssertionDisableFailAction, kA));
  EXPECT_TRUE(api.Control(vpiAssertionDisableFailAction, kA));
  EXPECT_FALSE(api.AssertionFailActionEnabled(kA));

  EXPECT_TRUE(api.Control(vpiAssertionEnablePassAction, kA));
  EXPECT_TRUE(api.Control(vpiAssertionEnablePassAction, kA));
  EXPECT_TRUE(api.AssertionPassActionEnabled(kA));
}

// §39.5.2: a control constant that is not part of this subclause is rejected by
// every per-assertion control entry point.
TEST(AssertionControl, UnrecognizedControlRejected) {
  AssertionApi api;
  // vpiAssertionSysOff belongs to §39.5.1 system control, not per-assertion
  // control, so it is not a valid operator here.
  EXPECT_FALSE(api.Control(vpiAssertionSysOff, kA));
  EXPECT_FALSE(
      api.ControlAttempt(vpiAssertionSysOff, kA, /*attempt_start_time=*/10));
  EXPECT_FALSE(api.ControlStep(vpiAssertionSysOff, kA,
                               /*attempt_start_time=*/10,
                               vpiAssertionClockSteps));
}

// §39.5.2 vpiAssertionLock: while locked, the status cannot be changed through
// any control entry point, including the attempt and step controls; only an
// unlock proceeds.
TEST(AssertionControl, LockBlocksAttemptAndStepControls) {
  AssertionApi api;
  api.NoteAssertionAttemptStarted(kA, 10);
  EXPECT_TRUE(api.Control(vpiAssertionLock, kA));

  // Reset, kill, disable-step, and enable-step are all rejected while locked.
  EXPECT_FALSE(api.Control(vpiAssertionReset, kA));
  EXPECT_FALSE(
      api.ControlAttempt(vpiAssertionKill, kA, /*attempt_start_time=*/10));
  EXPECT_FALSE(api.ControlAttempt(vpiAssertionDisableStep, kA,
                                  /*attempt_start_time=*/10));
  EXPECT_FALSE(api.ControlStep(vpiAssertionEnableStep, kA,
                               /*attempt_start_time=*/10,
                               vpiAssertionClockSteps));

  // State is unchanged: the attempt is still in progress and stepping is off.
  EXPECT_EQ(api.AssertionAttemptsInProgress(kA), 1u);
  EXPECT_FALSE(api.AssertionStepEnabled(kA, 10));
}

// §39.5.2 vpiAssertionKill: killing an attempt that is not in progress (no
// matching start time) is a harmless no-op and does not disturb other attempts.
TEST(AssertionControl, KillUnknownAttemptIsNoOp) {
  AssertionApi api;
  api.NoteAssertionAttemptStarted(kA, 10);

  EXPECT_TRUE(
      api.ControlAttempt(vpiAssertionKill, kA, /*attempt_start_time=*/99));
  EXPECT_EQ(api.AssertionAttemptsInProgress(kA), 1u);
}

// §39.5.2 vpiAssertionDisableStep: disabling step for an attempt that was never
// stepping has no effect.
TEST(AssertionControl, DisableStepNoEffectWhenNotStepping) {
  AssertionApi api;
  api.NoteAssertionAttemptStarted(kA, 10);

  EXPECT_TRUE(api.ControlAttempt(vpiAssertionDisableStep, kA,
                                 /*attempt_start_time=*/10));
  EXPECT_FALSE(api.AssertionStepEnabled(kA, 10));
}

// §39.5.2 vpiAssertionEnableStep: enabling step when it is already enabled for
// the attempt has no effect (idempotent).
TEST(AssertionControl, EnableStepIsIdempotent) {
  AssertionApi api;
  EXPECT_TRUE(api.ControlStep(vpiAssertionEnableStep, kA,
                              /*attempt_start_time=*/30,
                              vpiAssertionClockSteps));
  EXPECT_TRUE(api.ControlStep(vpiAssertionEnableStep, kA,
                              /*attempt_start_time=*/30,
                              vpiAssertionClockSteps));
  EXPECT_TRUE(api.AssertionStepEnabled(kA, 30));
}

// Two assertions, one of them unnamed, each failing at each of three clock
// edges, their fail actions counting the failures, the design calling $arm
// between the edges.
constexpr const char* kTwoFailing =
    "module top;\n"
    "  logic clk = 0, a = 0;\n"
    "  int f1 = 0, f2 = 0, f3 = 0;\n"
    "  a1: assert property (@(posedge clk) a) else f1++;\n"
    "  a2: assert property (@(posedge clk) a) else f2++;\n"
    "  assert property (@(posedge clk) a) else f3++;\n"
    "  initial begin\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0; $arm;\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0; $arm;\n"
    "    #5 clk = 1;\n"
    "  end\n"
    "endmodule\n";

// A design whose assertion a1, of `property`, fails each attempt two clock
// edges after it begins, at the third and the fourth edge, the design calling
// $arm after the first.
std::string AttemptsInFlight(const std::string& property) {
  return "module top;\n"
         "  logic clk = 0, a = 0;\n"
         "  a1: assert property (@(posedge clk) " +
         property +
         ") else begin end\n"
         "  initial begin\n"
         "    #5 clk = 1;\n"
         "    #5 clk = 0; $arm;\n"
         "    #5 clk = 1;\n"
         "    #5 clk = 0;\n"
         "    #5 clk = 1;\n"
         "    #5 clk = 0;\n"
         "    #5 clk = 1;\n"
         "  end\n"
         "endmodule\n";
}

// Watches a1's failures and kills its attempt begun at 5.
void KillAttemptBegunAt5() {
  ASSERT_NE(WatchAssertion("top.a1", cbAssertionFailure), nullptr);
  s_vpi_time start = {vpiSimTime, 0, 5, 0.0};
  EXPECT_EQ(vpi_control(vpiAssertionKill,
                        vpi_handle_by_name(VpiText("top.a1"), nullptr), &start),
            1);
}

// Calls vpi_control(`operation`, the assertion `full_name` names).
std::function<void()> Control(int operation, const char* full_name) {
  return [operation, full_name] {
    EXPECT_EQ(
        vpi_control(operation, vpi_handle_by_name(VpiText(full_name), nullptr)),
        1);
  };
}

// The start time of each failed attempt the failure callback saw, in order.
std::vector<uint64_t> FailedAttemptStarts() {
  std::vector<uint64_t> starts;
  for (const AssertionCall& call : AssertionRun::CallsOf(cbAssertionFailure)) {
    starts.push_back(call.attempt_start);
  }
  return starts;
}

// §39.5.2: vpiAssertionDisable stops the one assertion it is handed from
// starting attempts until vpiAssertionEnable, the assertion beside it going
// on failing (#7502).
TEST_F(AssertionRun, DisableStopsOneAssertionsAttemptsUntilEnable) {
  ArmInTurn({Control(vpiAssertionDisable, "top.a1"),
             Control(vpiAssertionEnable, "top.a1")});
  Run(kTwoFailing);

  EXPECT_EQ(IntOf("top.f1"), 2);
  EXPECT_EQ(IntOf("top.f2"), 3);
  EXPECT_EQ(IntOf("top.f3"), 3);
}

// §39.5.2: vpiAssertionDisableFailAction stops the assertion's fail action
// while its attempts still fail, as the failure callback sees (#7502).
TEST_F(AssertionRun, DisableFailActionStopsOneAssertionsFailAction) {
  ArmInTurn({[] {
    ASSERT_NE(WatchAssertion("top.a1", cbAssertionFailure), nullptr);
    Control(vpiAssertionDisableFailAction, "top.a1")();
  }});
  Run(kTwoFailing);

  EXPECT_EQ(IntOf("top.f1"), 1);
  EXPECT_EQ(IntOf("top.f2"), 3);
  EXPECT_EQ(CallsOf(cbAssertionFailure).size(), 2u);
}

// §39.5.2 with §39.3.1: an unnamed assertion's handle, reached by
// iteration, is controlled as a named one's is (#7502).
TEST_F(AssertionRun, DisableStopsAnUnnamedAssertion) {
  ArmInTurn({[] {
    vpiHandle unnamed = UnnamedAssertOf("top");
    ASSERT_NE(unnamed, nullptr);
    EXPECT_EQ(vpi_control(vpiAssertionDisable, unnamed), 1);
  }});
  Run(kTwoFailing);

  EXPECT_EQ(IntOf("top.f1"), 3);
  EXPECT_EQ(IntOf("top.f3"), 1);
}

// §39.5.2: vpiAssertionReset discards the assertion's attempt in flight and
// leaves it starting attempts as it did at the outset (#7502).
TEST_F(AssertionRun, ResetDiscardsTheAttemptInFlight) {
  ArmInTurn({[] {
    ASSERT_NE(WatchAssertion("top.a1", cbAssertionFailure), nullptr);
    Control(vpiAssertionReset, "top.a1")();
  }});
  Run(AttemptsInFlight("1 |-> ##2 a"));

  EXPECT_EQ(FailedAttemptStarts(), (std::vector<uint64_t>{15}));
}

// §39.5.2: vpiAssertionKill discards the one attempt that began at the time
// it is handed, the assertion going on with the rest; with no control both
// attempts fail (#7503).
TEST_F(AssertionRun, KillDiscardsTheAttemptBegunAtTheTimeHanded) {
  ArmInTurn({KillAttemptBegunAt5});
  Run(AttemptsInFlight("1 |-> ##2 a"));

  EXPECT_EQ(FailedAttemptStarts(), (std::vector<uint64_t>{15}));
}

// §39.5.2: the same of an assertion whose property is a sequence, whose
// attempts the run keeps apart from those of a property of operators.
TEST_F(AssertionRun, KillDiscardsTheSequenceAttemptBegunAtTheTimeHanded) {
  ArmInTurn({KillAttemptBegunAt5});
  Run(AttemptsInFlight("1 ##2 a"));

  EXPECT_EQ(FailedAttemptStarts(), (std::vector<uint64_t>{15}));
}

TEST_F(AssertionRun, WithNoControlEveryAttemptFails) {
  ArmInTurn({[] {
    ASSERT_NE(WatchAssertion("top.a1", cbAssertionFailure), nullptr);
  }});
  Run(AttemptsInFlight("1 |-> ##2 a"));

  EXPECT_EQ(FailedAttemptStarts(), (std::vector<uint64_t>{5, 15}));
}

}  // namespace
