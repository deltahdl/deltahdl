#include <gtest/gtest.h>

#include <iterator>

#include "simulator/dpi_runtime.h"
#include "simulator/sv_vpi_user.h"

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

// §39.5.2 intro: only assertion statement handles (assert/assume/cover) are
// valid; sequence and property instances are not.
TEST(AssertionControl, OnlyAssertionStatementHandlesValid) {
  EXPECT_TRUE(AssertionApi::IsAssertionStatementHandle(vpiAssert));
  EXPECT_TRUE(AssertionApi::IsAssertionStatementHandle(vpiAssume));
  EXPECT_TRUE(AssertionApi::IsAssertionStatementHandle(vpiCover));
  EXPECT_TRUE(AssertionApi::IsAssertionStatementHandle(vpiImmediateAssert));

  EXPECT_FALSE(AssertionApi::IsAssertionStatementHandle(vpiSequenceDecl));
  EXPECT_FALSE(AssertionApi::IsAssertionStatementHandle(vpiProperty));
  EXPECT_FALSE(AssertionApi::IsAssertionStatementHandle(vpiPropertyDecl));
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

}  // namespace
