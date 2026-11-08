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

TEST(DeferredAssertionQueue, PendingInstancesAreQueuedAndCounted) {
  AssertionApi api;
  EXPECT_EQ(api.PendingAssertionReportCount(kA), 0u);

  api.QueuePendingAssertionReport(kA);
  api.QueuePendingAssertionReport(kA);
  EXPECT_EQ(api.PendingAssertionReportCount(kA), 2u);
}

TEST(DeferredAssertionQueue, DisableLeavesPendingReportsToMature) {
  AssertionApi api;
  api.NoteAssertionAttemptStarted(kA, 10);
  api.QueuePendingAssertionReport(kA);

  EXPECT_TRUE(api.Control(vpiAssertionDisable, kA));

  EXPECT_EQ(api.PendingAssertionReportCount(kA), 1u);
  EXPECT_FALSE(api.AssertionEnabled(kA));
}

TEST(DeferredAssertionQueue, ResetFlushOnlyTargetedAssertion) {
  AssertionApi api;
  api.QueuePendingAssertionReport(kA);
  api.QueuePendingAssertionReport(kB);

  EXPECT_TRUE(api.Control(vpiAssertionReset, kA));

  EXPECT_EQ(api.PendingAssertionReportCount(kA), 0u);
  EXPECT_EQ(api.PendingAssertionReportCount(kB), 1u);
}

TEST(DeferredAssertionQueue, NonDiscardControlsDoNotFlush) {
  for (int control :
       {vpiAssertionEnable, vpiAssertionLock, vpiAssertionUnlock,
        vpiAssertionDisablePassAction, vpiAssertionEnablePassAction,
        vpiAssertionDisableFailAction, vpiAssertionEnableFailAction,
        vpiAssertionDisableVacuousAction, vpiAssertionEnableNonvacuousAction}) {
    AssertionApi api;
    api.QueuePendingAssertionReport(kA);
    EXPECT_TRUE(api.Control(control, kA));
    EXPECT_EQ(api.PendingAssertionReportCount(kA), 1u);
  }
}

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

TEST(DeferredAssertionQueue, SystemNonDiscardControlsDoNotFlush) {
  for (int control :
       {vpiAssertionSysOff, vpiAssertionSysOn, vpiAssertionSysLock,
        vpiAssertionSysUnlock, vpiAssertionSysDisablePassAction,
        vpiAssertionSysEnablePassAction, vpiAssertionSysDisableFailAction,
        vpiAssertionSysEnableFailAction, vpiAssertionSysDisableVacuousAction,
        vpiAssertionSysEnableNonvacuousAction}) {
    AssertionApi api;
    api.QueuePendingAssertionReport(kA);
    api.QueuePendingAssertionReport(kB);

    EXPECT_TRUE(api.SysControl(control));

    EXPECT_EQ(api.PendingAssertionReportCount(kA), 1u);
    EXPECT_EQ(api.PendingAssertionReportCount(kB), 1u);
  }
}

TEST(DeferredAssertionQueue, ResetWithNoPendingReportsIsHarmless) {
  AssertionApi api;
  ASSERT_EQ(api.PendingAssertionReportCount(kA), 0u);

  EXPECT_TRUE(api.Control(vpiAssertionReset, kA));

  EXPECT_EQ(api.PendingAssertionReportCount(kA), 0u);
}

TEST(DeferredAssertionQueue, RejectedDiscardControlDoesNotFlush) {
  AssertionApi api;
  api.QueuePendingAssertionReport(kA);
  ASSERT_TRUE(api.Control(vpiAssertionLock, kA));

  EXPECT_FALSE(api.Control(vpiAssertionReset, kA));

  EXPECT_EQ(api.PendingAssertionReportCount(kA), 1u);
}

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

TEST_F(DeferredAssertionQueueThroughVpiControl, ResetFlushesWhatIsQueued) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);
  api_.NoteAssertionAttemptStarted(kA, 10);
  api_.QueuePendingAssertionReport(kA);
  api_.QueuePendingAssertionReport(kA);

  EXPECT_EQ(vpi_control(vpiAssertionReset, assertion), 1);

  EXPECT_EQ(api_.AssertionAttemptsInProgress(kA), 0u);
  EXPECT_EQ(api_.PendingAssertionReportCount(kA), 0u);
}

TEST_F(DeferredAssertionQueueThroughVpiControl, DisableLeavesTheQueueStanding) {
  VpiHandle assertion = vpi_ctx_.CreateAssertion(kA, vpiAssert);
  api_.NoteAssertionAttemptStarted(kA, 10);
  api_.QueuePendingAssertionReport(kA);

  EXPECT_EQ(vpi_control(vpiAssertionDisable, assertion), 1);

  EXPECT_FALSE(api_.AssertionEnabled(kA));
  EXPECT_EQ(api_.AssertionAttemptsInProgress(kA), 1u);
  EXPECT_EQ(api_.PendingAssertionReportCount(kA), 1u);
}

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

constexpr const char* kDeferredFailing =
    "module top;\n"
    "  logic x = 0;\n"
    "  int failed1 = 0, failed2 = 0;\n"
    "  function void fail1(); failed1++; endfunction\n"
    "  function void fail2(); failed2++; endfunction\n"
    "  initial begin\n"
    "    a1: assert #0 (x) else fail1();\n"
    "    a2: assert #0 (x) else fail2();\n"
    "    $arm;\n"
    "  end\n"
    "endmodule\n";

std::function<void()> Control(int operation, const char* full_name) {
  return [operation, full_name] {
    vpiHandle target = full_name == nullptr
                           ? nullptr
                           : vpi_handle_by_name(VpiText(full_name), nullptr);
    EXPECT_EQ(vpi_control(operation, target), 1);
  };
}

TEST_F(AssertionRun, ResetFlushesADeferredAssertionsQueuedReport) {
  ArmInTurn({Control(vpiAssertionReset, "top.a1")});
  Run(kDeferredFailing);

  EXPECT_EQ(IntOf("top.failed1"), 0);
  EXPECT_EQ(IntOf("top.failed2"), 1);
}

TEST_F(AssertionRun, SysKillFlushesADeferredAssertionsQueuedReport) {
  ArmInTurn({Control(vpiAssertionSysKill, nullptr)});
  Run(kDeferredFailing);

  EXPECT_EQ(IntOf("top.failed1"), 0);
  EXPECT_EQ(IntOf("top.failed2"), 0);
}

TEST_F(AssertionRun, DisableLeavesADeferredAssertionsQueuedReport) {
  ArmInTurn({Control(vpiAssertionDisable, "top.a1")});
  Run(kDeferredFailing);

  EXPECT_EQ(IntOf("top.failed1"), 1);
  EXPECT_EQ(IntOf("top.failed2"), 1);
}

constexpr const char* kProceduralFailing =
    "module top;\n"
    "  logic clk = 0, a = 0;\n"
    "  int failed1 = 0, failed2 = 0;\n"
    "  always @(posedge clk) begin\n"
    "    c1: assert property (a) else failed1++;\n"
    "    c2: assert property (a) else failed2++;\n"
    "    $arm;\n"
    "  end\n"
    "  initial begin\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0;\n"
    "    #5 clk = 1;\n"
    "  end\n"
    "endmodule\n";

TEST_F(AssertionRun, ResetFlushesAProceduralAssertionsPendingInstance) {
  ArmInTurn({Control(vpiAssertionReset, "top.c1")});
  Run(kProceduralFailing);

  EXPECT_EQ(IntOf("top.failed1"), 1);
  EXPECT_EQ(IntOf("top.failed2"), 2);
}

TEST_F(AssertionRun, WithNoControlEachPendingInstanceFails) {
  Run(kProceduralFailing);

  EXPECT_EQ(IntOf("top.failed1"), 2);
  EXPECT_EQ(IntOf("top.failed2"), 2);
}

}  // namespace
