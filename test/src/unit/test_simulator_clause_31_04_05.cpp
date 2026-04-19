#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §31.4.5 Table 31-11: a $period entry stores an edge-qualified
// reference signal and a limit, with no data signal — the data event is
// derived from the reference event.
TEST(TimingCheckCommandSim, PeriodEntryStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kPeriod;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 50;
  mgr.AddTimingCheck(tc);
  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  const auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kPeriod);
  EXPECT_EQ(stored.ref_signal, "clk");
  EXPECT_EQ(stored.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_TRUE(stored.data_signal.empty());
  EXPECT_EQ(stored.limit, 50u);
}

// §31.4.5 violation predicate: (timecheck time) - (timestamp time) <
// limit. An elapsed time strictly less than the limit must report a
// violation.
TEST(TimingCheckCommandSim, PeriodElapsedBelowLimitViolates) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kPeriod;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 50;
  mgr.AddTimingCheck(tc);
  // elapsed = 30 < limit = 50 → violation.
  EXPECT_TRUE(mgr.CheckPeriodViolation("clk", /*ref_time=*/100,
                                       /*data_time=*/130));
}

// §31.4.5 violation predicate has a strict upper bound: an elapsed time
// equal to the limit is not a violation.
TEST(TimingCheckCommandSim, PeriodElapsedAtLimitNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kPeriod;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 50;
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckPeriodViolation("clk", /*ref_time=*/100,
                                        /*data_time=*/150));
}

// §31.4.5 violation predicate: an elapsed time strictly greater than the
// limit means the period was long enough and reports no violation.
TEST(TimingCheckCommandSim, PeriodElapsedAboveLimitNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kPeriod;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 50;
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckPeriodViolation("clk", /*ref_time=*/100,
                                        /*data_time=*/200));
}

// §31.4.5: the data event is derived from the reference event with the
// same edge, so a non-greater data_time is not a meaningful interval and
// reports no violation.
TEST(TimingCheckCommandSim, PeriodSimultaneousNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kPeriod;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 50;
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckPeriodViolation("clk", /*ref_time=*/100,
                                        /*data_time=*/100));
}

// §31.4.5: a $period entry is keyed on its reference signal — events on
// an unrelated signal do not trigger the check.
TEST(TimingCheckCommandSim, PeriodMismatchedSignalIgnored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kPeriod;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 50;
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckPeriodViolation("other", /*ref_time=*/100,
                                        /*data_time=*/130));
}

// §31.4.5: non-$period entries in the manager must not be considered by
// the $period violation predicate.
TEST(TimingCheckCommandSim, PeriodOtherKindsIgnored) {
  SpecifyManager mgr;
  TimingCheckEntry width;
  width.kind = TimingCheckKind::kWidth;
  width.ref_signal = "clk";
  width.limit = 50;
  mgr.AddTimingCheck(width);
  EXPECT_FALSE(mgr.CheckPeriodViolation("clk", /*ref_time=*/100,
                                        /*data_time=*/130));
}

// §31.4.5 Syntax 31-13: a $period invocation in a specify block must
// elaborate and lower end-to-end without disturbing the surrounding
// simulation.
TEST(TimingCheckCommandSim, PeriodSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $period(posedge clk, 50);\n"
      "  endspecify\n"
      "  initial x = 8'd77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

}  // namespace
