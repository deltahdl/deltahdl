#include "fixture_simulator.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

TEST(TimingCheckCommandSim, NochangeDataInsideWindowViolates) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  mgr.AddTimingCheck(tc);
  EXPECT_TRUE(mgr.CheckNochangeViolation("clk", 100, 200, "data", 150));
}

TEST(TimingCheckCommandSim, NochangeDataAtLeadingEdgeNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", 100, 200, "data", 100));
}

TEST(TimingCheckCommandSim, NochangeDataAtTrailingEdgeNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", 100, 200, "data", 200));
}

TEST(TimingCheckCommandSim, NochangePositiveStartOffsetExtendsRegion) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  tc.start_edge_offset = 20;
  mgr.AddTimingCheck(tc);

  EXPECT_TRUE(mgr.CheckNochangeViolation("clk", 100, 200, "data", 90));
}

TEST(TimingCheckCommandSim, NochangeNegativeStartOffsetShrinksRegion) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  tc.start_edge_offset = -20;
  mgr.AddTimingCheck(tc);

  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", 100, 200, "data", 110));
}

TEST(TimingCheckCommandSim, NochangePositiveEndOffsetExtendsRegion) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  tc.end_edge_offset = 20;
  mgr.AddTimingCheck(tc);

  EXPECT_TRUE(mgr.CheckNochangeViolation("clk", 100, 200, "data", 210));
}

TEST(TimingCheckCommandSim, NochangeNegativeEndOffsetShrinksRegion) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  tc.end_edge_offset = -20;
  mgr.AddTimingCheck(tc);

  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", 100, 200, "data", 190));
}

TEST(TimingCheckCommandSim, NochangeMismatchedSignalIgnored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckNochangeViolation("other", 100, 200, "data", 150));
}

TEST(TimingCheckCommandSim, NochangeMismatchedDataSignalIgnored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", 100, 200, "other", 150));
}

TEST(TimingCheckCommandSim, NochangeOtherKindsIgnored) {
  SpecifyManager mgr;
  TimingCheckEntry setup;
  setup.kind = TimingCheckKind::kSetup;
  setup.ref_signal = "clk";
  setup.data_signal = "data";
  setup.limit = 50;
  mgr.AddTimingCheck(setup);
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", 100, 200, "data", 150));
}

}  // namespace
