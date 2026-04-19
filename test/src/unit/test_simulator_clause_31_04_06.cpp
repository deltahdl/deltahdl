#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §31.4.6 Table 31-12: a $nochange entry stores the edge-qualified
// reference signal, the data signal, and the two edge offsets.
TEST(TimingCheckCommandSim, NochangeEntryStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  tc.start_edge_offset = 3;
  tc.end_edge_offset = 5;
  mgr.AddTimingCheck(tc);
  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  const auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kNochange);
  EXPECT_EQ(stored.ref_signal, "clk");
  EXPECT_EQ(stored.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(stored.data_signal, "data");
  EXPECT_EQ(stored.start_edge_offset, 3);
  EXPECT_EQ(stored.end_edge_offset, 5);
}

// §31.4.6: with both offsets zero the violation region spans the
// reference signal's level interval. A data event strictly inside the
// interval witnesses a violation.
TEST(TimingCheckCommandSim, NochangeDataInsideWindowViolates) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  mgr.AddTimingCheck(tc);
  EXPECT_TRUE(mgr.CheckNochangeViolation("clk", /*leading=*/100,
                                         /*trailing=*/200, "data",
                                         /*data_time=*/150));
}

// §31.4.6: "(beginning of time window) < (data event time) < (end of
// time window)" — the endpoints are strictly excluded, so a data event
// at the leading reference edge does not violate.
TEST(TimingCheckCommandSim, NochangeDataAtLeadingEdgeNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", /*leading=*/100,
                                          /*trailing=*/200, "data",
                                          /*data_time=*/100));
}

// §31.4.6: the trailing-edge endpoint is also strictly excluded — a
// data event at the trailing reference edge does not violate.
TEST(TimingCheckCommandSim, NochangeDataAtTrailingEdgeNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", /*leading=*/100,
                                          /*trailing=*/200, "data",
                                          /*data_time=*/200));
}

// §31.4.6: data events that land before the window opens report no
// violation.
TEST(TimingCheckCommandSim, NochangeDataBeforeWindowNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", /*leading=*/100,
                                          /*trailing=*/200, "data",
                                          /*data_time=*/50));
}

// §31.4.6: data events that land past the window closes report no
// violation.
TEST(TimingCheckCommandSim, NochangeDataAfterWindowNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", /*leading=*/100,
                                          /*trailing=*/200, "data",
                                          /*data_time=*/250));
}

// §31.4.6: "A positive offset for start edge extends the region by
// starting the timing violation region earlier." A data event that
// precedes the leading reference edge but falls inside the extended
// region witnesses a violation.
TEST(TimingCheckCommandSim, NochangePositiveStartOffsetExtendsRegion) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  tc.start_edge_offset = 20;
  mgr.AddTimingCheck(tc);
  // leading - start_edge_offset = 80 < 90 < 200.
  EXPECT_TRUE(mgr.CheckNochangeViolation("clk", /*leading=*/100,
                                         /*trailing=*/200, "data",
                                         /*data_time=*/90));
}

// §31.4.6: "a negative offset for start edge shrinks the region by
// starting the region later." A data event inside the original level
// interval but before the shrunken start no longer violates.
TEST(TimingCheckCommandSim, NochangeNegativeStartOffsetShrinksRegion) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  tc.start_edge_offset = -20;
  mgr.AddTimingCheck(tc);
  // leading - start_edge_offset = 120; data at 110 sits before the
  // shrunken start and does not violate.
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", /*leading=*/100,
                                          /*trailing=*/200, "data",
                                          /*data_time=*/110));
}

// §31.4.6: "a positive offset for the end edge extends the timing
// violation region by ending it later." A data event past the trailing
// reference edge but inside the extended region violates.
TEST(TimingCheckCommandSim, NochangePositiveEndOffsetExtendsRegion) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  tc.end_edge_offset = 20;
  mgr.AddTimingCheck(tc);
  // trailing + end_edge_offset = 220; data at 210 falls inside.
  EXPECT_TRUE(mgr.CheckNochangeViolation("clk", /*leading=*/100,
                                         /*trailing=*/200, "data",
                                         /*data_time=*/210));
}

// §31.4.6: "a negative offset for the end edge shrinks the region by
// ending it earlier." A data event before the original trailing edge
// but past the shrunken end no longer violates.
TEST(TimingCheckCommandSim, NochangeNegativeEndOffsetShrinksRegion) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  tc.end_edge_offset = -20;
  mgr.AddTimingCheck(tc);
  // trailing + end_edge_offset = 180; data at 190 falls past the
  // shrunken end and does not violate.
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", /*leading=*/100,
                                          /*trailing=*/200, "data",
                                          /*data_time=*/190));
}

// §31.4.6: the two offsets compose — with both start_edge_offset and
// end_edge_offset positive the violation region extends on both sides
// of the reference level interval. A data event outside the
// unextended interval but inside the combined extension violates.
TEST(TimingCheckCommandSim, NochangeBothPositiveOffsetsExtendRegion) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  tc.start_edge_offset = 10;
  tc.end_edge_offset = 10;
  mgr.AddTimingCheck(tc);
  // begin = 100 - 10 = 90; end = 200 + 10 = 210. Both endpoint
  // extensions independently admit a violation.
  EXPECT_TRUE(mgr.CheckNochangeViolation("clk", /*leading=*/100,
                                         /*trailing=*/200, "data",
                                         /*data_time=*/95));
  EXPECT_TRUE(mgr.CheckNochangeViolation("clk", /*leading=*/100,
                                         /*trailing=*/200, "data",
                                         /*data_time=*/205));
}

// §31.4.6: the violation predicate is the strict inequality
// "(beginning of time window) < (data event time) < (end of time
// window)". Negative offsets large enough to drive begin ≥ end yield
// an empty region that can never report a violation, no matter where
// the data event lands.
TEST(TimingCheckCommandSim, NochangeCollapsedRegionNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  // leading=100, trailing=200, start_off=-60, end_off=-60
  // begin = 100 - (-60) = 160; end = 200 + (-60) = 140. begin > end.
  tc.start_edge_offset = -60;
  tc.end_edge_offset = -60;
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", 100, 200, "data", 150));
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", 100, 200, "data", 130));
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", 100, 200, "data", 170));
}

// §31.4.6: a $nochange entry is keyed on its reference signal — events
// on an unrelated reference signal do not trigger the check.
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

// §31.4.6: the data_signal field also keys the entry — a transition on
// an unrelated data signal does not trigger the check.
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

// §31.4.6: non-$nochange entries in the manager must not be considered
// by the $nochange violation predicate.
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

// §31.4.6 Syntax 31-14: start_edge_offset and end_edge_offset are
// mintypmax_expression productions; a full min:typ:max triple in each
// offset position must lower end-to-end without disturbing the rest of
// the simulation.
TEST(TimingCheckCommandSim, NochangeMinTypMaxOffsetsSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $nochange(posedge clk, data, 1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "  initial x = 8'd10;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// §31.4.6 Syntax 31-14: a $nochange invocation in a specify block
// must elaborate and lower end-to-end without disturbing the
// surrounding simulation.
TEST(TimingCheckCommandSim, NochangeSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $nochange(posedge clk, data, 0, 0);\n"
      "  endspecify\n"
      "  initial x = 8'd42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

}  // namespace
