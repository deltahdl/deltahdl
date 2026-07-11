#include <gtest/gtest.h>

#include <iterator>

#include "simulator/dpi_runtime.h"
#include "simulator/sv_vpi_user.h"

using namespace delta;

namespace {

// §39.5.1: the six assertion-system action-control constants must exist and be
// distinct from one another within the assertion-control constant group.
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

// §39.5.1 C1/C2: a control is accepted with a scope; a null (empty) scope means
// the control applies to all assertions regardless of scope.
TEST(AssertionSysControl, NullScopeAppliesGlobally) {
  AssertionApi api;
  EXPECT_TRUE(api.SysControl(vpiAssertionSysOff, {}));
  EXPECT_TRUE(api.LastControlGlobal());

  EXPECT_TRUE(api.SysControl(vpiAssertionSysOn, "top.scope_a"));
  EXPECT_FALSE(api.LastControlGlobal());
}

// §39.5.1 C4: SysOff disables further starts; executing attempts unaffected;
// preexisting callbacks unaffected.
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

// §39.5.1 C5: SysKill discards attempts in progress and disables further
// starts; callbacks unaffected.
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

// §39.5.1 C8: SysOn restarts the system so attempts resume; prior callbacks
// unaffected.
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

// §39.5.1 C3: SysReset discards attempts, restores initial state, removes step
// success/failure callbacks, and keeps all other callbacks.
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

  EXPECT_EQ(api.CallbackCount(), 1u);  // only the non-step callback remains
  EXPECT_EQ(api.AttemptsInProgress(), 0u);
  EXPECT_TRUE(api.AssertionsStarted());  // back to initial running state
  EXPECT_TRUE(api.FailActionEnabled());  // action enables restored
  EXPECT_TRUE(api.PassActionEnabled());
}

// §39.5.1 C3 (input form): "restores the entire assertion system to its initial
// state" must re-enable a pass action that was disabled before the reset, not
// just the fail action. Disabling the pass action clears both the vacuous and
// nonvacuous components; the reset restores all of them to enabled.
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

// §39.5.1 C8 (input form): SysOn restarts the system after suspension caused by
// SysKill, the second cause the description names. SysKill also discards the
// attempts in progress, so resuming must leave starts re-enabled while the
// discarded attempts stay gone; preexisting callbacks are unaffected.
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
  EXPECT_EQ(api.AttemptsInProgress(), 0u);  // killed attempts do not return
  EXPECT_EQ(api.CallbackCount(), 1u);       // callback unaffected
}

// §39.5.1 C6/C7: SysLock blocks status changes until SysUnlock.
TEST(AssertionSysControl, LockBlocksStatusChangesUntilUnlock) {
  AssertionApi api;
  api.SysControl(vpiAssertionSysLock, {});

  EXPECT_TRUE(api.SysLocked());
  EXPECT_FALSE(
      api.SysControl(vpiAssertionSysOff, {}));  // rejected while locked
  EXPECT_TRUE(api.AssertionsStarted());         // unchanged

  EXPECT_TRUE(api.SysControl(vpiAssertionSysUnlock, {}));  // unlock is allowed
  EXPECT_FALSE(api.SysLocked());
  EXPECT_TRUE(api.SysControl(vpiAssertionSysOff, {}));
  EXPECT_FALSE(api.AssertionsStarted());
}

// §39.5.1 C9: SysEnd discards attempts, disables starts, removes all callbacks,
// and permits no further assertion actions.
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
  // Any later control is rejected once the system has ended.
  EXPECT_FALSE(api.SysControl(vpiAssertionSysOn, {}));
  EXPECT_FALSE(api.AssertionsStarted());
}

// §39.5.1 C10/C11: pass-action enable/disable affects both vacuous and
// nonvacuous success; default is enabled.
TEST(AssertionSysControl, PassActionEnableDisable) {
  AssertionApi api;
  EXPECT_TRUE(api.PassActionEnabled());  // default enabled

  api.SysControl(vpiAssertionSysDisablePassAction, {});
  EXPECT_FALSE(api.PassActionEnabled());
  EXPECT_FALSE(api.VacuousActionEnabled());
  EXPECT_FALSE(api.NonvacuousActionEnabled());

  api.SysControl(vpiAssertionSysEnablePassAction, {});
  EXPECT_TRUE(api.PassActionEnabled());
  EXPECT_TRUE(api.VacuousActionEnabled());
  EXPECT_TRUE(api.NonvacuousActionEnabled());
}

// §39.5.1 C12/C13: fail-action enable/disable; default is enabled.
TEST(AssertionSysControl, FailActionEnableDisable) {
  AssertionApi api;
  EXPECT_TRUE(api.FailActionEnabled());  // default enabled

  api.SysControl(vpiAssertionSysDisableFailAction, {});
  EXPECT_FALSE(api.FailActionEnabled());

  api.SysControl(vpiAssertionSysEnableFailAction, {});
  EXPECT_TRUE(api.FailActionEnabled());
}

// §39.5.1 C14/C15: vacuous-only disable and nonvacuous-only enable act on the
// individual components of the pass action; default is enabled.
TEST(AssertionSysControl, VacuousAndNonvacuousIndividualControl) {
  AssertionApi api;
  EXPECT_TRUE(api.VacuousActionEnabled());  // defaults enabled

  api.SysControl(vpiAssertionSysDisableVacuousAction, {});
  EXPECT_FALSE(api.VacuousActionEnabled());
  EXPECT_TRUE(api.NonvacuousActionEnabled());  // nonvacuous unaffected

  api.SysControl(vpiAssertionSysDisablePassAction, {});
  ASSERT_FALSE(api.NonvacuousActionEnabled());
  api.SysControl(vpiAssertionSysEnableNonvacuousAction, {});
  EXPECT_TRUE(api.NonvacuousActionEnabled());
  EXPECT_FALSE(api.VacuousActionEnabled());  // vacuous unaffected
}

// §39.5.1 C1 (error path): an unrecognized control constant is rejected and
// leaves the system state untouched.
TEST(AssertionSysControl, UnknownControlRejected) {
  AssertionApi api;
  EXPECT_FALSE(api.SysControl(/*control=*/0, {}));
  EXPECT_FALSE(api.SysControl(vpiAssertionSysReset - 12345, {}));

  EXPECT_TRUE(api.AssertionsStarted());
  EXPECT_FALSE(api.SysLocked());
  EXPECT_FALSE(api.SysEnded());
  EXPECT_TRUE(api.PassActionEnabled());
  EXPECT_TRUE(api.FailActionEnabled());
}

// §39.5.1 C6 (edge): while locked, action controls are blocked just like
// on/off controls, since the status cannot be changed without unlocking.
TEST(AssertionSysControl, LockBlocksActionControls) {
  AssertionApi api;
  api.SysControl(vpiAssertionSysLock, {});

  EXPECT_FALSE(api.SysControl(vpiAssertionSysDisableFailAction, {}));
  EXPECT_TRUE(api.FailActionEnabled());  // unchanged while locked
  EXPECT_FALSE(api.SysControl(vpiAssertionSysDisablePassAction, {}));
  EXPECT_TRUE(api.PassActionEnabled());  // unchanged while locked

  api.SysControl(vpiAssertionSysUnlock, {});
  EXPECT_TRUE(api.SysControl(vpiAssertionSysDisableFailAction, {}));
  EXPECT_FALSE(api.FailActionEnabled());
}

// §39.5.1 C9 (edge): once the system has ended, no further action is permitted
// at all — even an unlock control is rejected.
TEST(AssertionSysControl, EndBlocksEveryFurtherControl) {
  AssertionApi api;
  api.SysControl(vpiAssertionSysEnd, {});
  ASSERT_TRUE(api.SysEnded());

  EXPECT_FALSE(api.SysControl(vpiAssertionSysUnlock, {}));
  EXPECT_FALSE(api.SysControl(vpiAssertionSysReset, {}));
  EXPECT_FALSE(api.SysControl(vpiAssertionSysEnablePassAction, {}));
  EXPECT_TRUE(api.SysEnded());  // remains ended
}

}  // namespace
