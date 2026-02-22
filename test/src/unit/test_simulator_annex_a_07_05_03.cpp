// Tests for A.7.5.3 — System timing check event definitions — Simulation

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/specify.h"
#include "simulation/variable.h"

using namespace delta;

namespace {

struct SimA70503Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimA70503Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

} // namespace

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

// Runtime TimingCheckEntry stores negedge correctly
TEST(SimA70503, RuntimeTimingCheckEntryNegedge) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kHold;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kNegedge;
  tc.data_signal = "data";
  tc.limit = 5;
  mgr.AddTimingCheck(tc);
  EXPECT_EQ(mgr.GetTimingChecks()[0].ref_edge, SpecifyEdge::kNegedge);
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
// A.7.5.3 Sim — End-to-end: timing check events with edge controls
// =============================================================================

// Module with timing check using edge keyword simulates
TEST(SimA70503, EdgeKeywordSimulates) {
  SimA70503Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  specify\n"
                              "    $setup(data, edge clk, 10);\n"
                              "  endspecify\n"
                              "  initial x = 8'd42;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// Module with edge_control_specifier simulates
TEST(SimA70503, EdgeControlSpecifierSimulates) {
  SimA70503Fixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] x;\n"
                              "  specify\n"
                              "    $setup(data, edge [01, 10] clk, 10);\n"
                              "  endspecify\n"
                              "  initial x = 8'd55;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

// =============================================================================
// A.7.5.3 Sim — End-to-end: specify_terminal_descriptor with ranges
// =============================================================================

// Terminal with bit select simulates
TEST(SimA70503, TerminalBitSelectSimulates) {
  SimA70503Fixture f;
  auto *design = ElaborateSrc("module t;\n"
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
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

// Terminal with part select simulates
TEST(SimA70503, TerminalPartSelectSimulates) {
  SimA70503Fixture f;
  auto *design = ElaborateSrc("module t;\n"
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
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

// =============================================================================
// A.7.5.3 Sim — End-to-end: timing_check_condition with &&&
// =============================================================================

// Timing check with &&& condition simulates
TEST(SimA70503, TimingCheckConditionSimulates) {
  SimA70503Fixture f;
  auto *design = ElaborateSrc("module t;\n"
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
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

// Conditions on both events simulate
TEST(SimA70503, ConditionBothEventsSimulates) {
  SimA70503Fixture f;
  auto *design =
      ElaborateSrc("module t;\n"
                   "  logic [7:0] x;\n"
                   "  specify\n"
                   "    $hold(posedge clk &&& en, data &&& reset, 5);\n"
                   "  endspecify\n"
                   "  initial x = 8'd66;\n"
                   "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 66u);
}

// =============================================================================
// A.7.5.3 Sim — End-to-end: controlled_timing_check_event
// =============================================================================

// $period with controlled event simulates
TEST(SimA70503, ControlledTimingCheckEventPeriodSimulates) {
  SimA70503Fixture f;
  auto *design = ElaborateSrc("module t;\n"
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
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// Full combination: edge control + bit-select + condition simulates
TEST(SimA70503, FullCombinationSimulates) {
  SimA70503Fixture f;
  auto *design =
      ElaborateSrc("module t;\n"
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
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}
