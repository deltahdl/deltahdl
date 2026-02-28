// Annex A.7.5.3: System timing check event definitions

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.3 Sim — Runtime TimingCheckEntry edge storage
// =============================================================================
// Runtime TimingCheckEntry stores ref_edge correctly
TEST(SimA70503, RuntimeTimingCheckEntryEdges) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetup;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  tc.data_edge = SpecifyEdge::kNone;
  tc.limit = 10;
  mgr.AddTimingCheck(tc);
  EXPECT_EQ(mgr.GetTimingChecks()[0].ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(mgr.GetTimingChecks()[0].data_edge, SpecifyEdge::kNone);
}

// Runtime TimingCheckEntry stores edge keyword correctly
TEST(SimA70503, RuntimeTimingCheckEntryEdgeKw) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetup;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kEdge;
  tc.data_signal = "data";
  tc.limit = 10;
  mgr.AddTimingCheck(tc);
  EXPECT_EQ(mgr.GetTimingChecks()[0].ref_edge, SpecifyEdge::kEdge);
}

// =============================================================================
// A.7.5.3 Sim — End-to-end: specify_terminal_descriptor with ranges
// =============================================================================
// Terminal with bit select simulates
TEST(SimA70503, TerminalBitSelectSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setup(data[0], posedge clk, 10);\n"
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

// Terminal with part select simulates
TEST(SimA70503, TerminalPartSelectSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setup(data[3:0], posedge clk, 10);\n"
      "  endspecify\n"
      "  initial x = 8'd88;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

// =============================================================================
// A.7.5.3 Sim — End-to-end: timing_check_condition with &&&
// =============================================================================
// Timing check with &&& condition simulates
TEST(SimA70503, TimingCheckConditionSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setup(data &&& en, posedge clk, 10);\n"
      "  endspecify\n"
      "  initial x = 8'd33;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

// =============================================================================
// A.7.5.3 Sim — End-to-end: controlled_timing_check_event
// =============================================================================
// $period with controlled event simulates
TEST(SimA70503, ControlledTimingCheckEventPeriodSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $period(posedge clk, 50);\n"
      "  endspecify\n"
      "  initial x = 8'd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// Full combination: edge control + bit-select + condition simulates
TEST(SimA70503, FullCombinationSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $hold(posedge clk &&& en, data[0] &&& reset, 5);\n"
      "  endspecify\n"
      "  initial x = 8'd11;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

}  // namespace
