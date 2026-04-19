#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §31.4.4 Table 31-10: a $width entry stores an edge-qualified reference
// signal, a limit, and a threshold — with no data signal (derived from
// the reference event).
TEST(TimingCheckCommandSim, WidthEntryStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  tc.threshold = 1;
  mgr.AddTimingCheck(tc);
  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  const auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kWidth);
  EXPECT_EQ(stored.ref_signal, "clk");
  EXPECT_EQ(stored.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_TRUE(stored.data_signal.empty());
  EXPECT_EQ(stored.limit, 20u);
  EXPECT_EQ(stored.threshold, 1u);
}

// §31.4.4: "it is permissible to not specify both the threshold and
// notifier arguments, making the default value for the threshold zero."
TEST(TimingCheckCommandSim, WidthThresholdDefaultsToZero) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  mgr.AddTimingCheck(tc);
  EXPECT_EQ(mgr.GetTimingChecks()[0].threshold, 0u);
}

// §31.4.4 violation predicate: threshold < elapsed < limit. An elapsed
// time strictly between threshold and limit must report a violation.
TEST(TimingCheckCommandSim, WidthElapsedBetweenThresholdAndLimitViolates) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  tc.threshold = 1;
  mgr.AddTimingCheck(tc);
  // elapsed = 10: 1 < 10 < 20 → violation.
  EXPECT_TRUE(mgr.CheckWidthViolation("clk", /*ref_time=*/100,
                                      /*data_time=*/110));
}

// §31.4.4 violation predicate has a strict upper bound: elapsed equal to
// `limit` is not a violation.
TEST(TimingCheckCommandSim, WidthElapsedAtLimitNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckWidthViolation("clk", /*ref_time=*/100,
                                       /*data_time=*/120));
}

// §31.4.4: the threshold lower bound is also strict — elapsed equal to
// the threshold is ignored (a glitch pulse at exactly threshold is not a
// violation).
TEST(TimingCheckCommandSim, WidthElapsedAtThresholdNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  tc.threshold = 5;
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckWidthViolation("clk", /*ref_time=*/100,
                                       /*data_time=*/105));
}

// §31.4.4 glitch-suppression purpose of threshold: a pulse strictly
// narrower than the threshold is filtered out and must not produce a
// violation even though it is also narrower than the limit.
TEST(TimingCheckCommandSim, WidthElapsedBelowThresholdNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  tc.threshold = 5;
  mgr.AddTimingCheck(tc);
  // elapsed = 3: 3 < threshold=5, glitch pulse → no violation.
  EXPECT_FALSE(mgr.CheckWidthViolation("clk", /*ref_time=*/100,
                                       /*data_time=*/103));
}

// §31.4.4 violation predicate has a strict upper bound: a pulse whose
// width exceeds `limit` is wider than the required minimum and must not
// report a violation.
TEST(TimingCheckCommandSim, WidthElapsedAboveLimitNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  mgr.AddTimingCheck(tc);
  // elapsed = 30: wider than limit=20, pulse is long enough → no violation.
  EXPECT_FALSE(mgr.CheckWidthViolation("clk", /*ref_time=*/100,
                                       /*data_time=*/130));
}

// §31.4.4: the data event must follow the reference event in time; a
// non-greater data_time is not a valid width interval and reports no
// violation.
TEST(TimingCheckCommandSim, WidthSimultaneousNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckWidthViolation("clk", /*ref_time=*/100,
                                       /*data_time=*/100));
}

// §31.4.4: a $width entry is keyed on its reference signal — pulses on
// an unrelated signal do not trigger the check.
TEST(TimingCheckCommandSim, WidthMismatchedSignalIgnored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckWidthViolation("other", /*ref_time=*/100,
                                       /*data_time=*/110));
}

// §31.4.4: non-$width entries in the manager must not be considered by
// the $width violation predicate.
TEST(TimingCheckCommandSim, WidthOtherKindsIgnored) {
  SpecifyManager mgr;
  TimingCheckEntry setup;
  setup.kind = TimingCheckKind::kSetup;
  setup.ref_signal = "clk";
  setup.data_signal = "data";
  setup.limit = 20;
  mgr.AddTimingCheck(setup);
  EXPECT_FALSE(mgr.CheckWidthViolation("clk", /*ref_time=*/100,
                                       /*data_time=*/110));
}

// §31.4.4 Syntax 31-12: a $width invocation in a specify block must
// elaborate and lower end-to-end without disturbing the surrounding
// simulation.
TEST(TimingCheckCommandSim, WidthSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $width(posedge clk, 20, 1);\n"
      "  endspecify\n"
      "  initial x = 8'd55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

}  // namespace
