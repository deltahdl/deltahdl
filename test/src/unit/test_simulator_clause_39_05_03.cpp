#include <gtest/gtest.h>

#include "simulator/dpi_runtime.h"
#include "simulator/sv_vpi_user.h"

using namespace delta;

namespace {

constexpr const char* kA = "top.a1";
constexpr const char* kB = "top.a2";

// §39.5.3: a deferred or procedural concurrent assertion may have pending,
// not-yet-matured instances queued for it; the queue is observable and starts
// empty.
TEST(DeferredAssertionQueue, PendingInstancesAreQueuedAndCounted) {
  AssertionApi api;
  EXPECT_EQ(api.PendingAssertionReportCount(kA), 0u);

  api.QueuePendingAssertionReport(kA);
  api.QueuePendingAssertionReport(kA);
  EXPECT_EQ(api.PendingAssertionReportCount(kA), 2u);
}

// §39.5.3 example: vpiAssertionDisable disables the starting of new attempts
// without affecting existing attempts, so it does not interfere with current
// attempts and therefore leaves already-queued pending reports untouched —
// they may still mature and be reported.
TEST(DeferredAssertionQueue, DisableLeavesPendingReportsToMature) {
  AssertionApi api;
  api.NoteAssertionAttemptStarted(kA, 10);
  api.QueuePendingAssertionReport(kA);

  EXPECT_TRUE(api.Control(vpiAssertionDisable, kA));

  // The pending instance is neither affected nor flushed.
  EXPECT_EQ(api.PendingAssertionReportCount(kA), 1u);
  EXPECT_FALSE(api.AssertionEnabled(kA));
}

// §39.5.3: flushing on a discard control is scoped to the assertion whose
// attempts were discarded; other assertions' pending instances are untouched.
TEST(DeferredAssertionQueue, ResetFlushOnlyTargetedAssertion) {
  AssertionApi api;
  api.QueuePendingAssertionReport(kA);
  api.QueuePendingAssertionReport(kB);

  EXPECT_TRUE(api.Control(vpiAssertionReset, kA));

  EXPECT_EQ(api.PendingAssertionReportCount(kA), 0u);
  EXPECT_EQ(api.PendingAssertionReportCount(kB), 1u);
}

// §39.5.3: non-discard per-assertion controls do not interfere with current
// attempts, so none of them affect or flush the pending queue.
TEST(DeferredAssertionQueue, NonDiscardControlsDoNotFlush) {
  for (int control :
       {vpiAssertionEnable, vpiAssertionLock, vpiAssertionUnlock,
        vpiAssertionDisablePassAction, vpiAssertionEnablePassAction,
        vpiAssertionDisableFailAction, vpiAssertionEnableFailAction,
        vpiAssertionDisableVacuousAction, vpiAssertionEnableNonvacuousAction}) {
    // A fresh instance per control keeps each case independent of the others.
    AssertionApi api;
    api.QueuePendingAssertionReport(kA);
    EXPECT_TRUE(api.Control(control, kA));
    EXPECT_EQ(api.PendingAssertionReportCount(kA), 1u);
  }
}

// §39.5.3: the system-wide discard controls (vpiAssertionSysReset / SysKill /
// SysEnd) discard all attempts in progress, so each flushes the pending
// instances of every assertion.
TEST(DeferredAssertionQueue, SystemDiscardControlsFlushAllAssertions) {
  {
    AssertionApi api;
    api.QueuePendingAssertionReport(kA);
    api.QueuePendingAssertionReport(kB);
    EXPECT_TRUE(api.SysControl(vpiAssertionSysReset));
    EXPECT_EQ(api.PendingAssertionReportCount(kA), 0u);
    EXPECT_EQ(api.PendingAssertionReportCount(kB), 0u);
  }
  {
    AssertionApi api;
    api.QueuePendingAssertionReport(kA);
    api.QueuePendingAssertionReport(kB);
    EXPECT_TRUE(api.SysControl(vpiAssertionSysKill));
    EXPECT_EQ(api.PendingAssertionReportCount(kA), 0u);
    EXPECT_EQ(api.PendingAssertionReportCount(kB), 0u);
  }
  {
    AssertionApi api;
    api.QueuePendingAssertionReport(kA);
    api.QueuePendingAssertionReport(kB);
    EXPECT_TRUE(api.SysControl(vpiAssertionSysEnd));
    EXPECT_EQ(api.PendingAssertionReportCount(kA), 0u);
    EXPECT_EQ(api.PendingAssertionReportCount(kB), 0u);
  }
}

// §39.5.3: none of the system-wide controls that leave attempts in progress
// alone (e.g. vpiAssertionSysOff disables further starts but does not affect
// executing attempts; lock/unlock/on and the action toggles likewise do not
// discard) interfere with current attempts, so none of them flush the pending
// queues of any assertion.
TEST(DeferredAssertionQueue, SystemNonDiscardControlsDoNotFlush) {
  for (int control :
       {vpiAssertionSysOff, vpiAssertionSysOn, vpiAssertionSysLock,
        vpiAssertionSysUnlock, vpiAssertionSysDisablePassAction,
        vpiAssertionSysEnablePassAction, vpiAssertionSysDisableFailAction,
        vpiAssertionSysEnableFailAction, vpiAssertionSysDisableVacuousAction,
        vpiAssertionSysEnableNonvacuousAction}) {
    // A fresh instance per control keeps each case independent — in particular
    // a prior SysLock must not bleed into the next control's case.
    AssertionApi api;
    api.QueuePendingAssertionReport(kA);
    api.QueuePendingAssertionReport(kB);

    EXPECT_TRUE(api.SysControl(control));

    EXPECT_EQ(api.PendingAssertionReportCount(kA), 1u);
    EXPECT_EQ(api.PendingAssertionReportCount(kB), 1u);
  }
}

// §39.5.3 edge: a discard control applied to an assertion that has no pending
// instances queued is a harmless no-op — there is simply nothing to flush.
TEST(DeferredAssertionQueue, ResetWithNoPendingReportsIsHarmless) {
  AssertionApi api;
  ASSERT_EQ(api.PendingAssertionReportCount(kA), 0u);

  EXPECT_TRUE(api.Control(vpiAssertionReset, kA));

  EXPECT_EQ(api.PendingAssertionReportCount(kA), 0u);
}

// §39.5.3 edge: the flush is coupled to the discard actually happening. A
// locked assertion rejects vpiAssertionReset before any attempt is discarded,
// so its already-queued pending reports are left intact.
TEST(DeferredAssertionQueue, RejectedDiscardControlDoesNotFlush) {
  AssertionApi api;
  api.QueuePendingAssertionReport(kA);
  ASSERT_TRUE(api.Control(vpiAssertionLock, kA));

  // Reset is refused while locked, so nothing is discarded and nothing flushed.
  EXPECT_FALSE(api.Control(vpiAssertionReset, kA));

  EXPECT_EQ(api.PendingAssertionReportCount(kA), 1u);
}

}  // namespace
