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

TEST(AssertionControl, ImmediateAssumeAndCoverHandlesValid) {
  EXPECT_TRUE(AssertionApi::IsAssertionStatementHandle(vpiImmediateAssume));
  EXPECT_TRUE(AssertionApi::IsAssertionStatementHandle(vpiImmediateCover));
}

TEST(AssertionControl, EmptyHandleRejected) {
  AssertionApi api;
  EXPECT_FALSE(api.Control(vpiAssertionDisable, {}));
  EXPECT_FALSE(api.ControlAttempt(vpiAssertionKill, {}, 10));
  EXPECT_FALSE(
      api.ControlStep(vpiAssertionEnableStep, {}, 10, vpiAssertionClockSteps));
}

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

TEST(AssertionControl, LockBlocksChangesUntilUnlocked) {
  AssertionApi api;
  EXPECT_TRUE(api.Control(vpiAssertionLock, kA));
  EXPECT_TRUE(api.AssertionLocked(kA));

  EXPECT_FALSE(api.Control(vpiAssertionDisable, kA));
  EXPECT_TRUE(api.AssertionEnabled(kA));

  EXPECT_TRUE(api.Control(vpiAssertionUnlock, kA));
  EXPECT_FALSE(api.AssertionLocked(kA));
  EXPECT_TRUE(api.Control(vpiAssertionDisable, kA));
  EXPECT_FALSE(api.AssertionEnabled(kA));
}

TEST(AssertionControl, DisableLeavesExistingAttemptsEnableRestores) {
  AssertionApi api;
  api.NoteAssertionAttemptStarted(kA, 10);

  EXPECT_TRUE(api.Control(vpiAssertionDisable, kA));
  EXPECT_FALSE(api.AssertionEnabled(kA));
  EXPECT_EQ(api.AssertionAttemptsInProgress(kA), 1u);

  EXPECT_TRUE(api.Control(vpiAssertionEnable, kA));
  EXPECT_TRUE(api.AssertionEnabled(kA));
}

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

TEST(AssertionControl, FailActionToggles) {
  AssertionApi api;
  EXPECT_TRUE(api.Control(vpiAssertionDisableFailAction, kA));
  EXPECT_FALSE(api.AssertionFailActionEnabled(kA));
  EXPECT_TRUE(api.Control(vpiAssertionEnableFailAction, kA));
  EXPECT_TRUE(api.AssertionFailActionEnabled(kA));
}

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

TEST(AssertionControl, KillDiscardsGivenAttemptKeepsAssertionEnabled) {
  AssertionApi api;
  api.NoteAssertionAttemptStarted(kA, 10);
  api.NoteAssertionAttemptStarted(kA, 20);

  EXPECT_TRUE(api.ControlAttempt(vpiAssertionKill, kA, 10));

  EXPECT_EQ(api.AssertionAttemptsInProgress(kA), 1u);
  EXPECT_TRUE(api.AssertionEnabled(kA));
  EXPECT_TRUE(api.ControlAttempt(vpiAssertionKill, kA, 20));
  EXPECT_EQ(api.AssertionAttemptsInProgress(kA), 0u);
}

TEST(AssertionControl, KillPreservesAssertionStateUnlikeReset) {
  AssertionApi api;
  api.NoteAssertionAttemptStarted(kA, 10);
  api.NoteAssertionAttemptStarted(kA, 20);
  api.Control(vpiAssertionDisable, kA);
  api.Control(vpiAssertionDisableFailAction, kA);

  EXPECT_TRUE(api.ControlAttempt(vpiAssertionKill, kA, 10));

  EXPECT_EQ(api.AssertionAttemptsInProgress(kA), 1u);
  EXPECT_FALSE(api.AssertionEnabled(kA));
  EXPECT_FALSE(api.AssertionFailActionEnabled(kA));
}

TEST(AssertionControl, StepModeFrozenAfterAttemptStarts) {
  AssertionApi api;
  api.NoteAssertionAttemptStarted(kA, 40);
  EXPECT_TRUE(
      api.ControlStep(vpiAssertionEnableStep, kA, 40, vpiAssertionClockSteps));
  EXPECT_FALSE(api.AssertionStepEnabled(kA, 40));

  EXPECT_TRUE(
      api.ControlStep(vpiAssertionEnableStep, kA, 50, vpiAssertionClockSteps));
  EXPECT_TRUE(api.AssertionStepEnabled(kA, 50));
  api.NoteAssertionAttemptStarted(kA, 50);
  EXPECT_TRUE(api.AssertionStepEnabled(kA, 50));
}

TEST(AssertionControl, DisableStepClearsStepping) {
  AssertionApi api;
  api.ControlStep(vpiAssertionEnableStep, kA, 30, vpiAssertionClockSteps);
  ASSERT_TRUE(api.AssertionStepEnabled(kA, 30));

  EXPECT_TRUE(api.ControlAttempt(vpiAssertionDisableStep, kA, 30));
  EXPECT_FALSE(api.AssertionStepEnabled(kA, 30));

  EXPECT_TRUE(api.ControlAttempt(vpiAssertionDisableStep, kA, 30));
  EXPECT_FALSE(api.AssertionStepEnabled(kA, 30));
}

TEST(AssertionControl, EnableStepEnablesStepping) {
  AssertionApi api;
  EXPECT_FALSE(api.AssertionStepEnabled(kA, 30));
  EXPECT_TRUE(
      api.ControlStep(vpiAssertionEnableStep, kA, 30, vpiAssertionClockSteps));
  EXPECT_TRUE(api.AssertionStepEnabled(kA, 30));
}

TEST(AssertionControl, EnableStepRequiresStepControlConstant) {
  AssertionApi api;
  EXPECT_FALSE(
      api.ControlStep(vpiAssertionEnableStep, kA, 30, vpiAssertionEnable));
  EXPECT_FALSE(api.AssertionStepEnabled(kA, 30));

  EXPECT_TRUE(
      api.ControlStep(vpiAssertionEnableStep, kA, 30, vpiAssertionClockSteps));
  EXPECT_TRUE(api.AssertionStepEnabled(kA, 30));
}

TEST(AssertionControl, ControlsAreScopedPerAssertion) {
  AssertionApi api;
  EXPECT_TRUE(api.Control(vpiAssertionDisable, kA));
  EXPECT_FALSE(api.AssertionEnabled(kA));
  EXPECT_TRUE(api.AssertionEnabled("top.a2"));
}

TEST(AssertionControl, EnableDisableAreIdempotent) {
  AssertionApi api;
  EXPECT_TRUE(api.Control(vpiAssertionEnable, kA));
  EXPECT_TRUE(api.AssertionEnabled(kA));

  EXPECT_TRUE(api.Control(vpiAssertionDisable, kA));
  EXPECT_TRUE(api.Control(vpiAssertionDisable, kA));
  EXPECT_FALSE(api.AssertionEnabled(kA));
}

TEST(AssertionControl, ActionControlsAreIdempotent) {
  AssertionApi api;
  EXPECT_TRUE(api.Control(vpiAssertionDisableFailAction, kA));
  EXPECT_TRUE(api.Control(vpiAssertionDisableFailAction, kA));
  EXPECT_FALSE(api.AssertionFailActionEnabled(kA));

  EXPECT_TRUE(api.Control(vpiAssertionEnablePassAction, kA));
  EXPECT_TRUE(api.Control(vpiAssertionEnablePassAction, kA));
  EXPECT_TRUE(api.AssertionPassActionEnabled(kA));
}

TEST(AssertionControl, UnrecognizedControlRejected) {
  AssertionApi api;
  EXPECT_FALSE(api.Control(vpiAssertionSysOff, kA));
  EXPECT_FALSE(api.ControlAttempt(vpiAssertionSysOff, kA, 10));
  EXPECT_FALSE(
      api.ControlStep(vpiAssertionSysOff, kA, 10, vpiAssertionClockSteps));
}

TEST(AssertionControl, LockBlocksAttemptAndStepControls) {
  AssertionApi api;
  api.NoteAssertionAttemptStarted(kA, 10);
  EXPECT_TRUE(api.Control(vpiAssertionLock, kA));

  EXPECT_FALSE(api.Control(vpiAssertionReset, kA));
  EXPECT_FALSE(api.ControlAttempt(vpiAssertionKill, kA, 10));
  EXPECT_FALSE(api.ControlAttempt(vpiAssertionDisableStep, kA, 10));
  EXPECT_FALSE(
      api.ControlStep(vpiAssertionEnableStep, kA, 10, vpiAssertionClockSteps));

  EXPECT_EQ(api.AssertionAttemptsInProgress(kA), 1u);
  EXPECT_FALSE(api.AssertionStepEnabled(kA, 10));
}

TEST(AssertionControl, KillUnknownAttemptIsNoOp) {
  AssertionApi api;
  api.NoteAssertionAttemptStarted(kA, 10);

  EXPECT_TRUE(api.ControlAttempt(vpiAssertionKill, kA, 99));
  EXPECT_EQ(api.AssertionAttemptsInProgress(kA), 1u);
}

TEST(AssertionControl, DisableStepNoEffectWhenNotStepping) {
  AssertionApi api;
  api.NoteAssertionAttemptStarted(kA, 10);

  EXPECT_TRUE(api.ControlAttempt(vpiAssertionDisableStep, kA, 10));
  EXPECT_FALSE(api.AssertionStepEnabled(kA, 10));
}

TEST(AssertionControl, EnableStepIsIdempotent) {
  AssertionApi api;
  EXPECT_TRUE(
      api.ControlStep(vpiAssertionEnableStep, kA, 30, vpiAssertionClockSteps));
  EXPECT_TRUE(
      api.ControlStep(vpiAssertionEnableStep, kA, 30, vpiAssertionClockSteps));
  EXPECT_TRUE(api.AssertionStepEnabled(kA, 30));
}

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

void KillAttemptBegunAt5() {
  ASSERT_NE(WatchAssertion("top.a1", cbAssertionFailure), nullptr);
  s_vpi_time start = {vpiSimTime, 0, 5, 0.0};
  EXPECT_EQ(vpi_control(vpiAssertionKill,
                        vpi_handle_by_name(VpiText("top.a1"), nullptr), &start),
            1);
}

std::function<void()> Control(int operation, const char* full_name) {
  return [operation, full_name] {
    EXPECT_EQ(
        vpi_control(operation, vpi_handle_by_name(VpiText(full_name), nullptr)),
        1);
  };
}

std::vector<uint64_t> FailedAttemptStarts() {
  std::vector<uint64_t> starts;
  for (const AssertionCall& call : AssertionRun::CallsOf(cbAssertionFailure)) {
    starts.push_back(call.attempt_start);
  }
  return starts;
}

TEST_F(AssertionRun, DisableStopsOneAssertionsAttemptsUntilEnable) {
  ArmInTurn({Control(vpiAssertionDisable, "top.a1"),
             Control(vpiAssertionEnable, "top.a1")});
  Run(kTwoFailing);

  EXPECT_EQ(IntOf("top.f1"), 2);
  EXPECT_EQ(IntOf("top.f2"), 3);
  EXPECT_EQ(IntOf("top.f3"), 3);
}

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

TEST_F(AssertionRun, ResetDiscardsTheAttemptInFlight) {
  ArmInTurn({[] {
    ASSERT_NE(WatchAssertion("top.a1", cbAssertionFailure), nullptr);
    Control(vpiAssertionReset, "top.a1")();
  }});
  Run(AttemptsInFlight("1 |-> ##2 a"));

  EXPECT_EQ(FailedAttemptStarts(), (std::vector<uint64_t>{15}));
}

TEST_F(AssertionRun, KillDiscardsTheAttemptBegunAtTheTimeHanded) {
  ArmInTurn({KillAttemptBegunAt5});
  Run(AttemptsInFlight("1 |-> ##2 a"));

  EXPECT_EQ(FailedAttemptStarts(), (std::vector<uint64_t>{15}));
}

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
