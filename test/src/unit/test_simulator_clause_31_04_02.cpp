#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SystemTimingCheckSim, TimeskewEntryStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kTimeskew;
  tc.ref_signal = "clk1";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "clk2";
  tc.data_edge = SpecifyEdge::kPosedge;
  tc.limit = 5;
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kTimeskew);
  EXPECT_EQ(stored.ref_signal, "clk1");
  EXPECT_EQ(stored.data_signal, "clk2");
  EXPECT_EQ(stored.limit, 5u);
}

TEST(TimingCheckCommandSim, TimeskewWithFlagsSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, ntfr, 1, 0);\n"
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

TimingCheckEntry MakeTimeskew(uint64_t limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kTimeskew;
  tc.ref_signal = "clk1";
  tc.data_signal = "clk2";
  tc.limit = limit;
  return tc;
}

TEST(TimeskewTimingCheckWindow, DataStrictlyBeyondLimitViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(5));
  EXPECT_TRUE(mgr.CheckTimeskewViolation("clk1", 100, "clk2", 106));
}

TEST(TimeskewTimingCheckWindow, DataAtLimitDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(5));
  EXPECT_FALSE(mgr.CheckTimeskewViolation("clk1", 100, "clk2", 105));
}

TEST(TimeskewTimingCheckWindow, ZeroLimitSimultaneousDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(0));
  EXPECT_FALSE(mgr.CheckTimeskewViolation("clk1", 100, "clk2", 100));
}

TEST(TimeskewTimingCheckWindow, ZeroLimitAnyLaterDataViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(0));
  EXPECT_TRUE(mgr.CheckTimeskewViolation("clk1", 100, "clk2", 101));
}

TEST(TimeskewTimingCheckWindow, MismatchedDataSignalDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(5));
  EXPECT_FALSE(mgr.CheckTimeskewViolation("clk1", 100, "other", 200));
}

TEST(TimeskewTimingCheckWindow, MismatchedReferenceSignalDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeTimeskew(5));
  EXPECT_FALSE(mgr.CheckTimeskewViolation("other", 100, "clk2", 200));
}

TEST(TimeskewTimingCheckWindow, OtherKindsAreIgnored) {
  SpecifyManager mgr;
  TimingCheckEntry skew;
  skew.kind = TimingCheckKind::kSkew;
  skew.ref_signal = "clk1";
  skew.data_signal = "clk2";
  skew.limit = 1;
  mgr.AddTimingCheck(skew);
  EXPECT_FALSE(mgr.CheckTimeskewViolation("clk1", 100, "clk2", 200));
}

TEST(TimeskewModeOracle, TimerModeDataWithinLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 103, true,
                                        5,
                                        false));
}

TEST(TimeskewModeOracle, TimerModeDataAtLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 105, true,
                                        5,
                                        false));
}

TEST(TimeskewModeOracle, TimerModeDataBeyondLimitViolates) {
  EXPECT_TRUE(ReportsTimeskewViolation(100, 106, true,
                                       5,
                                       false));
}

TEST(TimeskewModeOracle, TimerModeNewReferenceAtLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 105, false,
                                        5,
                                        false));
}

TEST(TimeskewModeOracle, TimerModeNewReferenceBeyondLimitViolates) {
  EXPECT_TRUE(ReportsTimeskewViolation(100, 106, false,
                                       5,
                                       false));
}

TEST(TimeskewModeOracle, TimerModeSimultaneousDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 100, true,
                                        0,
                                        false));
}

TEST(TimeskewModeOracle, EventModeDataBeyondLimitViolates) {
  EXPECT_TRUE(ReportsTimeskewViolation(100, 106, true,
                                       5,
                                       true));
}

TEST(TimeskewModeOracle, EventModeDataAtLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 105, true,
                                        5,
                                        true));
}

TEST(TimeskewModeOracle, EventModeNewReferenceBeyondLimitDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 200, false,
                                        5,
                                        true));
}

TEST(TimeskewModeOracle, OutOfOrderEventDoesNotViolate) {
  EXPECT_FALSE(ReportsTimeskewViolation(100, 90, true,
                                        5,
                                        false));
  EXPECT_FALSE(ReportsTimeskewViolation(100, 90, true,
                                        5,
                                        true));
}

}
