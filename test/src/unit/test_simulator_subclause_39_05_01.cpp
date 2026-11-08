#include <gtest/gtest.h>

#include <cstddef>
#include <functional>
#include <iterator>

#include "helpers_assertion_run.h"
#include "simulator/assertion_api.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

TEST(SvVpiUser, AssertionSysActionControlConstants) {
  int values[] = {vpiAssertionSysDisablePassAction,
                  vpiAssertionSysEnablePassAction,
                  vpiAssertionSysDisableFailAction,
                  vpiAssertionSysEnableFailAction,
                  vpiAssertionSysDisableVacuousAction,
                  vpiAssertionSysEnableNonvacuousAction};
  for (size_t i = 0; i < std::size(values); ++i) {
    for (size_t j = i + 1; j < std::size(values); ++j) {
      EXPECT_NE(values[i], values[j]);
    }
  }
}

TEST(AssertionSysControl, NullScopeAppliesGlobally) {
  AssertionApi api;
  EXPECT_TRUE(api.SysControl(vpiAssertionSysOff, {}));
  EXPECT_TRUE(api.LastControlGlobal());

  EXPECT_TRUE(api.SysControl(vpiAssertionSysOn, "top.scope_a"));
  EXPECT_FALSE(api.LastControlGlobal());
}

TEST(AssertionSysControl, SysOffDisablesStartsKeepsAttemptsAndCallbacks) {
  AssertionApi api;
  api.RegisterCallback(
      cbAssertionStart, [](const AssertionCbData&) {}, nullptr);
  api.NoteAttemptStarted();
  api.NoteAttemptStarted();

  api.SysControl(vpiAssertionSysOff, {});

  EXPECT_FALSE(api.AssertionsStarted());
  EXPECT_EQ(api.AttemptsInProgress(), 2u);
  EXPECT_EQ(api.CallbackCount(), 1u);
}

TEST(AssertionSysControl, SysKillDiscardsAttemptsKeepsCallbacks) {
  AssertionApi api;
  api.RegisterCallback(
      cbAssertionSuccess, [](const AssertionCbData&) {}, nullptr);
  api.NoteAttemptStarted();

  api.SysControl(vpiAssertionSysKill, {});

  EXPECT_FALSE(api.AssertionsStarted());
  EXPECT_EQ(api.AttemptsInProgress(), 0u);
  EXPECT_EQ(api.CallbackCount(), 1u);
}

TEST(AssertionSysControl, SysOnResumesAttempts) {
  AssertionApi api;
  api.RegisterCallback(
      cbAssertionFailure, [](const AssertionCbData&) {}, nullptr);
  api.SysControl(vpiAssertionSysOff, {});
  ASSERT_FALSE(api.AssertionsStarted());

  api.SysControl(vpiAssertionSysOn, {});

  EXPECT_TRUE(api.AssertionsStarted());
  EXPECT_EQ(api.CallbackCount(), 1u);
}

TEST(AssertionSysControl, SysResetRemovesOnlyStepCallbacks) {
  AssertionApi api;
  api.RegisterCallback(
      cbAssertionStepSuccess, [](const AssertionCbData&) {}, nullptr);
  api.RegisterCallback(
      cbAssertionStepFailure, [](const AssertionCbData&) {}, nullptr);
  api.RegisterCallback(
      cbAssertionStart, [](const AssertionCbData&) {}, nullptr);
  api.NoteAttemptStarted();
  api.SysControl(vpiAssertionSysOff, {});
  api.SysControl(vpiAssertionSysDisableFailAction, {});

  api.SysControl(vpiAssertionSysReset, {});

  EXPECT_EQ(api.CallbackCount(), 1u);
  EXPECT_EQ(api.AttemptsInProgress(), 0u);
  EXPECT_TRUE(api.AssertionsStarted());
  EXPECT_TRUE(api.FailActionEnabled());
  EXPECT_TRUE(api.PassActionEnabled());
}

TEST(AssertionSysControl, SysResetRestoresDisabledPassAction) {
  AssertionApi api;
  api.SysControl(vpiAssertionSysDisablePassAction, {});
  ASSERT_FALSE(api.PassActionEnabled());
  ASSERT_FALSE(api.VacuousActionEnabled());
  ASSERT_FALSE(api.NonvacuousActionEnabled());

  api.SysControl(vpiAssertionSysReset, {});

  EXPECT_TRUE(api.PassActionEnabled());
  EXPECT_TRUE(api.VacuousActionEnabled());
  EXPECT_TRUE(api.NonvacuousActionEnabled());
}

TEST(AssertionSysControl, SysOnResumesAfterKill) {
  AssertionApi api;
  api.RegisterCallback(
      cbAssertionFailure, [](const AssertionCbData&) {}, nullptr);
  api.NoteAttemptStarted();
  api.SysControl(vpiAssertionSysKill, {});
  ASSERT_FALSE(api.AssertionsStarted());
  ASSERT_EQ(api.AttemptsInProgress(), 0u);

  api.SysControl(vpiAssertionSysOn, {});

  EXPECT_TRUE(api.AssertionsStarted());
  EXPECT_EQ(api.AttemptsInProgress(), 0u);
  EXPECT_EQ(api.CallbackCount(), 1u);
}

TEST(AssertionSysControl, LockBlocksStatusChangesUntilUnlock) {
  AssertionApi api;
  api.SysControl(vpiAssertionSysLock, {});

  EXPECT_TRUE(api.SysLocked());
  EXPECT_FALSE(api.SysControl(vpiAssertionSysOff, {}));
  EXPECT_TRUE(api.AssertionsStarted());

  EXPECT_TRUE(api.SysControl(vpiAssertionSysUnlock, {}));
  EXPECT_FALSE(api.SysLocked());
  EXPECT_TRUE(api.SysControl(vpiAssertionSysOff, {}));
  EXPECT_FALSE(api.AssertionsStarted());
}

TEST(AssertionSysControl, SysEndRemovesAllCallbacksAndBlocksFurtherActions) {
  AssertionApi api;
  api.RegisterCallback(
      cbAssertionStart, [](const AssertionCbData&) {}, nullptr);
  api.RegisterCallback(
      cbAssertionStepSuccess, [](const AssertionCbData&) {}, nullptr);
  api.NoteAttemptStarted();

  api.SysControl(vpiAssertionSysEnd, {});

  EXPECT_TRUE(api.SysEnded());
  EXPECT_EQ(api.CallbackCount(), 0u);
  EXPECT_EQ(api.AttemptsInProgress(), 0u);
  EXPECT_FALSE(api.AssertionsStarted());
  EXPECT_FALSE(api.SysControl(vpiAssertionSysOn, {}));
  EXPECT_FALSE(api.AssertionsStarted());
}

TEST(AssertionSysControl, PassActionEnableDisable) {
  AssertionApi api;
  EXPECT_TRUE(api.PassActionEnabled());

  api.SysControl(vpiAssertionSysDisablePassAction, {});
  EXPECT_FALSE(api.PassActionEnabled());
  EXPECT_FALSE(api.VacuousActionEnabled());
  EXPECT_FALSE(api.NonvacuousActionEnabled());

  api.SysControl(vpiAssertionSysEnablePassAction, {});
  EXPECT_TRUE(api.PassActionEnabled());
  EXPECT_TRUE(api.VacuousActionEnabled());
  EXPECT_TRUE(api.NonvacuousActionEnabled());
}

TEST(AssertionSysControl, FailActionEnableDisable) {
  AssertionApi api;
  EXPECT_TRUE(api.FailActionEnabled());

  api.SysControl(vpiAssertionSysDisableFailAction, {});
  EXPECT_FALSE(api.FailActionEnabled());

  api.SysControl(vpiAssertionSysEnableFailAction, {});
  EXPECT_TRUE(api.FailActionEnabled());
}

TEST(AssertionSysControl, VacuousAndNonvacuousIndividualControl) {
  AssertionApi api;
  EXPECT_TRUE(api.VacuousActionEnabled());

  api.SysControl(vpiAssertionSysDisableVacuousAction, {});
  EXPECT_FALSE(api.VacuousActionEnabled());
  EXPECT_TRUE(api.NonvacuousActionEnabled());

  api.SysControl(vpiAssertionSysDisablePassAction, {});
  ASSERT_FALSE(api.NonvacuousActionEnabled());
  api.SysControl(vpiAssertionSysEnableNonvacuousAction, {});
  EXPECT_TRUE(api.NonvacuousActionEnabled());
  EXPECT_FALSE(api.VacuousActionEnabled());
}

TEST(AssertionSysControl, UnknownControlRejected) {
  AssertionApi api;
  EXPECT_FALSE(api.SysControl(0, {}));
  EXPECT_FALSE(api.SysControl(vpiAssertionSysReset - 12345, {}));

  EXPECT_TRUE(api.AssertionsStarted());
  EXPECT_FALSE(api.SysLocked());
  EXPECT_FALSE(api.SysEnded());
  EXPECT_TRUE(api.PassActionEnabled());
  EXPECT_TRUE(api.FailActionEnabled());
}

TEST(AssertionSysControl, LockBlocksActionControls) {
  AssertionApi api;
  api.SysControl(vpiAssertionSysLock, {});

  EXPECT_FALSE(api.SysControl(vpiAssertionSysDisableFailAction, {}));
  EXPECT_TRUE(api.FailActionEnabled());
  EXPECT_FALSE(api.SysControl(vpiAssertionSysDisablePassAction, {}));
  EXPECT_TRUE(api.PassActionEnabled());

  api.SysControl(vpiAssertionSysUnlock, {});
  EXPECT_TRUE(api.SysControl(vpiAssertionSysDisableFailAction, {}));
  EXPECT_FALSE(api.FailActionEnabled());
}

TEST(AssertionSysControl, EndBlocksEveryFurtherControl) {
  AssertionApi api;
  api.SysControl(vpiAssertionSysEnd, {});
  ASSERT_TRUE(api.SysEnded());

  EXPECT_FALSE(api.SysControl(vpiAssertionSysUnlock, {}));
  EXPECT_FALSE(api.SysControl(vpiAssertionSysReset, {}));
  EXPECT_FALSE(api.SysControl(vpiAssertionSysEnablePassAction, {}));
  EXPECT_TRUE(api.SysEnded());
}

TEST(AssertionSysControl, SysEndRemovesCallbacksPlacedOnAssertions) {
  AssertionApi api;
  int calls = 0;
  api.PlaceAssertionCallback(
      cbAssertionFailure, "top.a1", vpiAssert,
      [&](const AssertionCallbackArgs&) { ++calls; }, nullptr);

  api.SysControl(vpiAssertionSysEnd, {});

  EXPECT_EQ(api.PlacedCallbackCount(), 0u);
  EXPECT_EQ(api.DeliverAssertionEvent("top.a1", cbAssertionFailure, 10, {}),
            0u);
  EXPECT_EQ(calls, 0);
}

TEST(AssertionSysControl, SysResetRemovesPlacedStepCallbacks) {
  AssertionApi api;
  int failures = 0;
  api.PlaceAssertionCallback(
      cbAssertionStepSuccess, "top.a1", vpiAssert,
      [](const AssertionCallbackArgs&) {}, nullptr);
  api.PlaceAssertionCallback(
      cbAssertionStepFailure, "top.a1", vpiAssert,
      [](const AssertionCallbackArgs&) {}, nullptr);
  api.PlaceAssertionCallback(
      cbAssertionFailure, "top.a1", vpiAssert,
      [&](const AssertionCallbackArgs&) { ++failures; }, nullptr);

  api.SysControl(vpiAssertionSysReset, {});

  EXPECT_EQ(api.PlacedCallbackCount(), 1u);
  EXPECT_EQ(api.DeliverAssertionEvent("top.a1", cbAssertionFailure, 10, {}),
            1u);
  EXPECT_EQ(failures, 1);
}

TEST(AssertionSysControl, SysLockBlocksPerAssertionControls) {
  AssertionApi api;
  api.SysControl(vpiAssertionSysLock, {});

  EXPECT_FALSE(api.Control(vpiAssertionDisable, "top.a1"));
  EXPECT_TRUE(api.AssertionEnabled("top.a1"));
  EXPECT_FALSE(api.ControlAttempt(vpiAssertionKill, "top.a1", 5));
  EXPECT_FALSE(api.ControlStep(vpiAssertionEnableStep, "top.a1", 5,
                               vpiAssertionClockSteps));
  EXPECT_FALSE(api.AssertionStepEnabled("top.a1", 5));

  api.SysControl(vpiAssertionSysUnlock, {});
  EXPECT_TRUE(api.Control(vpiAssertionDisable, "top.a1"));
  EXPECT_FALSE(api.AssertionEnabled("top.a1"));
}

TEST(AssertionSysControl, SysEndBlocksPerAssertionControls) {
  AssertionApi api;
  api.SysControl(vpiAssertionSysEnd, {});

  EXPECT_FALSE(api.Control(vpiAssertionDisable, "top.a1"));
  EXPECT_TRUE(api.AssertionEnabled("top.a1"));
  EXPECT_FALSE(api.ControlAttempt(vpiAssertionKill, "top.a1", 5));
  EXPECT_FALSE(api.ControlStep(vpiAssertionEnableStep, "top.a1", 5,
                               vpiAssertionClockSteps));
  EXPECT_FALSE(api.AssertionStepEnabled("top.a1", 5));
}

constexpr const char* kFailingInstances =
    "module m(input logic clk);\n"
    "  int fails = 0;\n"
    "  logic a = 0;\n"
    "  a1: assert property (@(posedge clk) a) else fails++;\n"
    "endmodule\n"
    "module top;\n"
    "  logic clk = 0;\n"
    "  m u1(clk);\n"
    "  m u2(clk);\n"
    "  initial begin\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0; $arm;\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0; $arm;\n"
    "    #5 clk = 1;\n"
    "  end\n"
    "endmodule\n";

constexpr const char* kAttemptInFlight =
    "module top;\n"
    "  logic clk = 0, a = 0;\n"
    "  int fails = 0;\n"
    "  a1: assert property (@(posedge clk) 1 |-> ##1 a) else fails++;\n"
    "  initial begin\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0; $arm;\n"
    "    #5 clk = 1;\n"
    "  end\n"
    "endmodule\n";

std::function<void()> SysControl(int operation, const char* scope = nullptr) {
  return [operation, scope] {
    vpiHandle handle = scope == nullptr
                           ? nullptr
                           : vpi_handle_by_name(VpiText(scope), nullptr);
    EXPECT_EQ(vpi_control(operation, handle), 1);
  };
}

TEST_F(AssertionRun, SysOffStopsTheRunsAttemptsUntilSysOn) {
  ArmInTurn({SysControl(vpiAssertionSysOff), SysControl(vpiAssertionSysOn)});
  Run(kFailingInstances);

  EXPECT_EQ(IntOf("top.u1.fails"), 2);
  EXPECT_EQ(IntOf("top.u2.fails"), 2);
}

TEST_F(AssertionRun, SysOffOfAScopeLeavesTheOtherInstanceRunning) {
  ArmInTurn({SysControl(vpiAssertionSysOff, "top.u1")});
  Run(kFailingInstances);

  EXPECT_EQ(IntOf("top.u1.fails"), 1);
  EXPECT_EQ(IntOf("top.u2.fails"), 3);
}

TEST_F(AssertionRun, SysDisableFailActionStopsTheFailActionsAlone) {
  ArmInTurn({[] {
               ASSERT_NE(WatchAssertion("top.u1.a1", cbAssertionFailure),
                         nullptr);
               SysControl(vpiAssertionSysDisableFailAction)();
             },
             SysControl(vpiAssertionSysEnableFailAction)});
  Run(kFailingInstances);

  EXPECT_EQ(IntOf("top.u1.fails"), 2);
  EXPECT_EQ(IntOf("top.u2.fails"), 2);
  EXPECT_EQ(CallsOf(cbAssertionFailure).size(), 2u);
}

TEST_F(AssertionRun, SysKillDiscardsTheAttemptInFlight) {
  ArmInTurn({SysControl(vpiAssertionSysKill)});
  Run(kAttemptInFlight);

  EXPECT_EQ(IntOf("top.fails"), 0);
}

TEST_F(AssertionRun, SysOffLetsTheAttemptInFlightRunOn) {
  ArmInTurn({SysControl(vpiAssertionSysOff)});
  Run(kAttemptInFlight);

  EXPECT_EQ(IntOf("top.fails"), 1);
}

}  // namespace
