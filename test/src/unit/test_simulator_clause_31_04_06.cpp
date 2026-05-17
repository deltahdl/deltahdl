#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

TEST(TimingCheckCommandSim, NochangeDataInsideWindowViolates) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  mgr.AddTimingCheck(tc);
  EXPECT_TRUE(mgr.CheckNochangeViolation("clk", 100,
                                         200, "data",
                                         150));
}

TEST(TimingCheckCommandSim, NochangeDataAtLeadingEdgeNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", 100,
                                          200, "data",
                                          100));
}

TEST(TimingCheckCommandSim, NochangeDataAtTrailingEdgeNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", 100,
                                          200, "data",
                                          200));
}

TEST(TimingCheckCommandSim, NochangeDataBeforeWindowNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", 100,
                                          200, "data",
                                          50));
}

TEST(TimingCheckCommandSim, NochangeDataAfterWindowNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", 100,
                                          200, "data",
                                          250));
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

  EXPECT_TRUE(mgr.CheckNochangeViolation("clk", 100,
                                         200, "data",
                                         90));
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

  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", 100,
                                          200, "data",
                                          110));
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

  EXPECT_TRUE(mgr.CheckNochangeViolation("clk", 100,
                                         200, "data",
                                         210));
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

  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", 100,
                                          200, "data",
                                          190));
}

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

  EXPECT_TRUE(mgr.CheckNochangeViolation("clk", 100,
                                         200, "data",
                                         95));
  EXPECT_TRUE(mgr.CheckNochangeViolation("clk", 100,
                                         200, "data",
                                         205));
}

TEST(TimingCheckCommandSim, NochangeCollapsedRegionNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";

  tc.start_edge_offset = -60;
  tc.end_edge_offset = -60;
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", 100, 200, "data", 150));
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", 100, 200, "data", 130));
  EXPECT_FALSE(mgr.CheckNochangeViolation("clk", 100, 200, "data", 170));
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

}
