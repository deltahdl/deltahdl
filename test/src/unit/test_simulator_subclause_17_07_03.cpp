#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler_event.h"
#include "simulator/checker_scheduling_semantics.h"
#include "simulator/scheduler.h"

using namespace delta;

namespace {

TEST(CheckerSchedulingSemantics, ChangeSensitiveConstructsAreReactive) {
  EXPECT_EQ(
      HomeRegionForCheckerStatement(CheckerStatementKind::kChangeSensitive),
      Region::kReactive);
}

TEST(CheckerSchedulingSemantics, BlockingStatementsAreReactive) {
  EXPECT_EQ(HomeRegionForCheckerStatement(CheckerStatementKind::kBlocking),
            Region::kReactive);
}

TEST(CheckerSchedulingSemantics, CheckerVariableNonblockingUpdatesAreReNBA) {
  EXPECT_EQ(HomeRegionForCheckerStatement(
                CheckerStatementKind::kCheckerVariableNonblocking),
            Region::kReNBA);
}

TEST(CheckerSchedulingSemantics, ReNBAIsProcessedAfterReactiveAndReInactive) {
  const Region kReNba = HomeRegionForCheckerStatement(
      CheckerStatementKind::kCheckerVariableNonblocking);
  VerifyThreeRegionOrder({Region::kReactive, "reactive"},
                         {Region::kReInactive, "reinactive"},
                         {kReNba, "renba"});
}

TEST(CheckerSchedulingSemantics, SequenceEndPointCaptureSpansReactiveToReNBA) {
  const Region kRhsEval =
      HomeRegionForCheckerStatement(CheckerStatementKind::kBlocking);
  const Region kVarUpdate = HomeRegionForCheckerStatement(
      CheckerStatementKind::kCheckerVariableNonblocking);
  EXPECT_EQ(kRhsEval, Region::kReactive);
  EXPECT_EQ(kVarUpdate, Region::kReNBA);
  EXPECT_NE(kRhsEval, kVarUpdate);
}

TEST(CheckerSchedulingSemantics,
     ConcurrentAssertionSchedulingInvariantAcrossAllRegions) {
  for (int i = 0; i < static_cast<int>(Region::kCOUNT); ++i) {
    const auto kR = static_cast<Region>(i);
    EXPECT_EQ(ConcurrentAssertionRegionInChecker(kR), kR);
  }
}

TEST(CheckerSchedulingSemantics,
     BlockingPlacementReusesProgramReactiveMapping) {
  EXPECT_EQ(HomeRegionForCheckerStatement(CheckerStatementKind::kBlocking),
            Scheduler::HomeRegionForReactiveBlockingAssign());
  EXPECT_EQ(
      HomeRegionForCheckerStatement(CheckerStatementKind::kChangeSensitive),
      Scheduler::HomeRegionForReactiveBlockingAssign());
}

TEST(CheckerSchedulingSemantics,
     CheckerVariableNonblockingReusesReactiveNBADual) {
  EXPECT_EQ(HomeRegionForCheckerStatement(
                CheckerStatementKind::kCheckerVariableNonblocking),
            Scheduler::ReactiveSetDualOf(Region::kNBA));
}

TEST(CheckerSchedulingSemantics, AlwaysFfReadsTheCheckersSequenceEndPoint) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "checker chk(logic a, logic clk);\n"
      "  sequence s; @(posedge clk) a ##1 a; endsequence\n"
      "  bit t;\n"
      "  int hits = 0;\n"
      "  always_ff @(posedge clk) t <= s.triggered;\n"
      "  always_ff @(posedge clk) if (s.triggered) hits <= hits + 1;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0, a = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(a, clk);\n"
      "  initial begin #2 a = 1; #30 a = 0; #20 $finish; end\n"
      "endmodule\n",
      f, "c.hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
}

}  // namespace
