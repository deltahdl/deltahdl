#include <gtest/gtest.h>

#include <functional>

#include "helpers_assertion_run.h"
#include "simulator/assertion_api.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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

// -----------------------------------------------------------------------------
// §39.5.3 speaks of every VPI function, which is what an application calls
// rather than what the model does underneath: the controls reach the queues
// through vpi_control(), and the rule about which of them flush is a rule about
// that routine's operations.
// -----------------------------------------------------------------------------

class DeferredAssertionQueueThroughVpiControl : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&vpi_ctx_);
    SetGlobalAssertionApi(&api_);
  }
  void TearDown() override {
    SetGlobalAssertionApi(nullptr);
    SetGlobalVpiContext(nullptr);
  }

  VpiContext vpi_ctx_;
  AssertionApi api_;
};

// §39.5.3: a function that throws away the attempts being evaluated also
// empties these queues of every pending instance not yet matured, and
// vpiAssertionReset is the clause's own example of one that does. Called on the
// assertion's handle, it takes the attempt and the queued reports together.
TEST_F(DeferredAssertionQueueThroughVpiControl, ResetFlushesWhatIsQueued) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);
  api_.NoteAssertionAttemptStarted(kA, 10);
  api_.QueuePendingAssertionReport(kA);
  api_.QueuePendingAssertionReport(kA);

  EXPECT_EQ(vpi_control(vpiAssertionReset, assertion), 1);

  EXPECT_EQ(api_.AssertionAttemptsInProgress(kA), 0u);
  EXPECT_EQ(api_.PendingAssertionReportCount(kA), 0u);
}

// §39.5.3: a function that leaves the current attempts alone leaves these
// queues alone too - vpiAssertionDisable stops new attempts starting and leaves
// the ones in progress, so the reports already queued can still mature and be
// reported.
TEST_F(DeferredAssertionQueueThroughVpiControl, DisableLeavesTheQueueStanding) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);
  api_.NoteAssertionAttemptStarted(kA, 10);
  api_.QueuePendingAssertionReport(kA);

  EXPECT_EQ(vpi_control(vpiAssertionDisable, assertion), 1);

  EXPECT_FALSE(api_.AssertionEnabled(kA));
  EXPECT_EQ(api_.AssertionAttemptsInProgress(kA), 1u);
  EXPECT_EQ(api_.PendingAssertionReportCount(kA), 1u);
}

// §39.5.3 over the whole system: the rule is about what a function does to
// attempts, so the system controls divide the same way. Killing the system
// discards every attempt in progress and flushes every queue with them; turning
// it off stops assertions starting and leaves both where they were.
TEST_F(DeferredAssertionQueueThroughVpiControl, TheSystemControlsDivideAlike) {
  api_.NoteAssertionAttemptStarted(kA, 10);
  api_.QueuePendingAssertionReport(kA);
  api_.QueuePendingAssertionReport(kB);

  EXPECT_EQ(vpi_control(vpiAssertionSysOff, static_cast<vpiHandle>(nullptr)),
            1);
  EXPECT_EQ(api_.PendingAssertionReportCount(kA), 1u);
  EXPECT_EQ(api_.PendingAssertionReportCount(kB), 1u);

  EXPECT_EQ(vpi_control(vpiAssertionSysKill, static_cast<vpiHandle>(nullptr)),
            1);
  EXPECT_EQ(api_.PendingAssertionReportCount(kA), 0u);
  EXPECT_EQ(api_.PendingAssertionReportCount(kB), 0u);
}

// -----------------------------------------------------------------------------
// §39.5.3 in a run: the queues are the run's own, a deferred assertion's
// pending reports and a procedural concurrent assertion's pending instances,
// and a control reaches them through the handle the design's assertion has.
// -----------------------------------------------------------------------------

// A deferred assertion a1 that fails once, its fail action a subroutine call
// counting the failure, the design calling $arm after it has executed and
// before its report matures in the Reactive region.
constexpr const char* kDeferredFailing =
    "module top;\n"
    "  logic x = 0;\n"
    "  int failed = 0;\n"
    "  function void fail(); failed++; endfunction\n"
    "  initial begin\n"
    "    a1: assert #0 (x) else fail();\n"
    "    $arm;\n"
    "  end\n"
    "endmodule\n";

// Calls vpi_control(`operation`) on the assertion `full_name` names, or on
// the whole system where it names none.
std::function<void()> Control(int operation, const char* full_name) {
  return [operation, full_name] {
    vpiHandle target = full_name == nullptr
                           ? nullptr
                           : vpi_handle_by_name(VpiText(full_name), nullptr);
    EXPECT_EQ(vpi_control(operation, target), 1);
  };
}

// §39.5.3: vpiAssertionReset discards the deferred assertion's attempts, and
// with them the report its failure queued, which never matures (#7514).
TEST_F(AssertionRun, ResetFlushesADeferredAssertionsQueuedReport) {
  ArmInTurn({Control(vpiAssertionReset, "top.a1")});
  Run(kDeferredFailing);

  EXPECT_EQ(IntOf("top.failed"), 0);
}

// §39.5.3: vpiAssertionSysKill discards every attempt in progress, the
// reports queued for them among them (#7514).
TEST_F(AssertionRun, SysKillFlushesADeferredAssertionsQueuedReport) {
  ArmInTurn({Control(vpiAssertionSysKill, nullptr)});
  Run(kDeferredFailing);

  EXPECT_EQ(IntOf("top.failed"), 0);
}

// §39.5.3: vpiAssertionDisable leaves the attempts in progress, so the report
// already queued matures and the fail action runs (#7514).
TEST_F(AssertionRun, DisableLeavesADeferredAssertionsQueuedReport) {
  ArmInTurn({Control(vpiAssertionDisable, "top.a1")});
  Run(kDeferredFailing);

  EXPECT_EQ(IntOf("top.failed"), 1);
}

// A procedural concurrent assertion c1 that fails at each of two clock ticks,
// the procedure calling $arm after queuing each instance, before it matures in
// the Observed region.
constexpr const char* kProceduralFailing =
    "module top;\n"
    "  logic clk = 0, a = 0;\n"
    "  int failed = 0;\n"
    "  always @(posedge clk) begin\n"
    "    c1: assert property (a) else failed++;\n"
    "    $arm;\n"
    "  end\n"
    "  initial begin\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0;\n"
    "    #5 clk = 1;\n"
    "  end\n"
    "endmodule\n";

// §39.5.3: vpiAssertionReset flushes the procedural assertion's pending
// instance, which begins no attempt; the instance the procedure queues at the
// next tick fails as before (#7514).
TEST_F(AssertionRun, ResetFlushesAProceduralAssertionsPendingInstance) {
  ArmInTurn({Control(vpiAssertionReset, "top.c1")});
  Run(kProceduralFailing);

  EXPECT_EQ(IntOf("top.failed"), 1);
}

// With no control both instances begin attempts that fail.
TEST_F(AssertionRun, WithNoControlEachPendingInstanceFails) {
  Run(kProceduralFailing);

  EXPECT_EQ(IntOf("top.failed"), 2);
}

}  // namespace
