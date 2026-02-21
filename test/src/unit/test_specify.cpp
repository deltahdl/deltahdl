// Tests for §30 Specify blocks, §31 Timing checks, §32 SDF annotation
// Tests both parser (AST) and runtime (SpecifyManager) features.

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/specify.h"

using namespace delta;

namespace {

// =============================================================================
// Parser test fixture
// =============================================================================

struct SpecifyTest : ::testing::Test {
 protected:
  CompilationUnit* Parse(const std::string& src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  // Helper: get first specify block from first module.
  ModuleItem* FirstSpecifyBlock(CompilationUnit* cu) {
    for (auto* item : cu->modules[0]->items) {
      if (item->kind == ModuleItemKind::kSpecifyBlock) return item;
    }
    return nullptr;
  }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

// =============================================================================
// §30.3 Path delay declarations
// =============================================================================

TEST_F(SpecifyTest, ParallelPathDelay) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  (a => b) = 5;\n"
      "endspecify\n"
      "endmodule\n");
  ASSERT_EQ(cu->modules.size(), 1u);
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(item->path.path_kind, SpecifyPathKind::kParallel);
  ASSERT_EQ(item->path.src_ports.size(), 1u);
  EXPECT_EQ(item->path.src_ports[0].name, "a");
  ASSERT_EQ(item->path.dst_ports.size(), 1u);
  EXPECT_EQ(item->path.dst_ports[0].name, "b");
  ASSERT_EQ(item->path.delays.size(), 1u);
}

TEST_F(SpecifyTest, FullPathDelay) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  (a *> b) = 10;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->path.path_kind, SpecifyPathKind::kFull);
}

TEST_F(SpecifyTest, PathDelayWithRiseFall) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  (a => b) = (3, 5);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto& delays = spec->specify_items[0]->path.delays;
  EXPECT_EQ(delays.size(), 2u);
}

TEST_F(SpecifyTest, PathDelayThreeValues) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  (a => b) = (2, 3, 4);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items[0]->path.delays.size(), 3u);
}

// =============================================================================
// §30.3.1 Edge-sensitive paths
// =============================================================================

TEST_F(SpecifyTest, PosedgePath) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  (posedge clk => q) = 10;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto* path = spec->specify_items[0];
  EXPECT_EQ(path->path.edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(path->path.src_ports[0].name, "clk");
  EXPECT_EQ(path->path.dst_ports[0].name, "q");
}

TEST_F(SpecifyTest, NegedgePath) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  (negedge clk => q) = 8;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(spec->specify_items[0]->path.edge, SpecifyEdge::kNegedge);
}

// =============================================================================
// §30.3.3 Conditional path delays
// =============================================================================

TEST_F(SpecifyTest, ConditionalIfPath) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  if (sel) (a => b) = 5;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto* path = spec->specify_items[0];
  EXPECT_EQ(path->kind, SpecifyItemKind::kPathDecl);
  EXPECT_NE(path->path.condition, nullptr);
  EXPECT_FALSE(path->path.is_ifnone);
}

TEST_F(SpecifyTest, IfnoneConditionalPath) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  ifnone (a => b) = 7;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_TRUE(spec->specify_items[0]->path.is_ifnone);
  EXPECT_EQ(spec->specify_items[0]->path.condition, nullptr);
}

// =============================================================================
// §30.2 Specparam declarations (inside specify)
// =============================================================================

TEST_F(SpecifyTest, SpecparamInsideSpecify) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  specparam tRISE = 10;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kSpecparam);
  EXPECT_EQ(item->param_name, "tRISE");
  EXPECT_NE(item->param_value, nullptr);
}

// =============================================================================
// §31 Timing checks
// =============================================================================

TEST_F(SpecifyTest, SetupTimingCheck) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(tc.ref_signal, "data");
  EXPECT_EQ(tc.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.data_signal, "clk");
  ASSERT_EQ(tc.limits.size(), 1u);
}

TEST_F(SpecifyTest, HoldTimingCheck) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk, data, 5);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kHold);
  EXPECT_EQ(tc.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.ref_signal, "clk");
  EXPECT_EQ(tc.data_signal, "data");
}

TEST_F(SpecifyTest, SetupholdTimingCheck) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kSetuphold);
  ASSERT_GE(tc.limits.size(), 2u);
}

TEST_F(SpecifyTest, RecoveryTimingCheck) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $recovery(posedge clk, rst, 8);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(spec->specify_items[0]->timing_check.check_kind,
            TimingCheckKind::kRecovery);
}

TEST_F(SpecifyTest, RemovalTimingCheck) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $removal(posedge clk, rst, 3);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(spec->specify_items[0]->timing_check.check_kind,
            TimingCheckKind::kRemoval);
}

TEST_F(SpecifyTest, RecremTimingCheck) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge clk, rst, 8, 3);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kRecrem);
  ASSERT_GE(tc.limits.size(), 2u);
}

TEST_F(SpecifyTest, WidthTimingCheck) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge clk, 20);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kWidth);
  EXPECT_EQ(tc.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.ref_signal, "clk");
  ASSERT_GE(tc.limits.size(), 1u);
}

TEST_F(SpecifyTest, PeriodTimingCheck) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $period(posedge clk, 50);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(spec->specify_items[0]->timing_check.check_kind,
            TimingCheckKind::kPeriod);
}

TEST_F(SpecifyTest, TimingCheckWithNotifier) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(spec->specify_items[0]->timing_check.notifier, "ntfr");
}

TEST_F(SpecifyTest, SkewTimingCheck) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(posedge clk1, negedge clk2, 3);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kSkew);
  EXPECT_EQ(tc.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.ref_signal, "clk1");
  EXPECT_EQ(tc.data_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(tc.data_signal, "clk2");
}

TEST_F(SpecifyTest, NochangeTimingCheck) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(posedge clk, data, 0, 0);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kNochange);
  ASSERT_GE(tc.limits.size(), 2u);
}

TEST_F(SpecifyTest, TimeskewTimingCheck) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $timeskew(posedge clk1, posedge clk2, 5);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kTimeskew);
  EXPECT_EQ(tc.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.ref_signal, "clk1");
  EXPECT_EQ(tc.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.data_signal, "clk2");
  ASSERT_EQ(tc.limits.size(), 1u);
}

TEST_F(SpecifyTest, FullskewTimingCheck) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $fullskew(posedge clk1, negedge clk2, 4, 6);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kFullskew);
  EXPECT_EQ(tc.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.data_edge, SpecifyEdge::kNegedge);
  ASSERT_GE(tc.limits.size(), 2u);
}

TEST_F(SpecifyTest, TimeskewWithNotifier) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $timeskew(posedge clk1, posedge clk2, 5, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kTimeskew);
  EXPECT_EQ(tc.notifier, "ntfr");
}

// =============================================================================
// §31.7 Conditioned events
// =============================================================================

TEST_F(SpecifyTest, ConditionedSetup) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& clr, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(tc.ref_signal, "data");
  EXPECT_NE(tc.ref_condition, nullptr);
}

TEST_F(SpecifyTest, ConditionedHoldBothSignals) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk &&& en, data &&& reset, 5);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kHold);
  EXPECT_NE(tc.ref_condition, nullptr);
  EXPECT_NE(tc.data_condition, nullptr);
}

// =============================================================================
// §31.9 Extended $setuphold arguments
// =============================================================================

TEST_F(SpecifyTest, SetupholdWithDelayedSignals) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, -10, 20, ntfr, , , dCLK, dD);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kSetuphold);
  EXPECT_EQ(tc.notifier, "ntfr");
  EXPECT_EQ(tc.delayed_ref, "dCLK");
  EXPECT_EQ(tc.delayed_data, "dD");
}

// =============================================================================
// §30.4 Pulsestyle and showcancelled
// =============================================================================

TEST_F(SpecifyTest, PulsestyleOnevent) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  pulsestyle_onevent out1;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_FALSE(item->is_ondetect);
  ASSERT_EQ(item->signal_list.size(), 1u);
  EXPECT_EQ(item->signal_list[0], "out1");
}

TEST_F(SpecifyTest, PulsestyleOndetect) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  pulsestyle_ondetect out1;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_TRUE(spec->specify_items[0]->is_ondetect);
}

TEST_F(SpecifyTest, Showcancelled) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  showcancelled out1;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_FALSE(item->is_noshowcancelled);
}

TEST_F(SpecifyTest, Noshowcancelled) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  noshowcancelled out1;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_TRUE(spec->specify_items[0]->is_noshowcancelled);
}

// =============================================================================
// Complex specify block with mixed items
// =============================================================================

TEST_F(SpecifyTest, MixedSpecifyBlockItems) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  specparam tPD = 5;\n"
      "  (a => b) = 5;\n"
      "  (a *> c) = (3, 4);\n"
      "  $setup(data, posedge clk, 10);\n"
      "  $hold(posedge clk, data, 5);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 5u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kSpecparam);
  EXPECT_EQ(spec->specify_items[1]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[2]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[3]->kind, SpecifyItemKind::kTimingCheck);
  EXPECT_EQ(spec->specify_items[4]->kind, SpecifyItemKind::kTimingCheck);
}

// =============================================================================
// §32 SDF annotation (runtime model)
// =============================================================================

TEST_F(SpecifyTest, SdfAnnotateModel) {
  // Test the runtime SpecifyManager SDF annotation support.
  SpecifyManager mgr;
  mgr.AnnotateSdf({"timing.sdf", "top.dut"});
  ASSERT_EQ(mgr.GetSdfAnnotations().size(), 1u);
  EXPECT_EQ(mgr.GetSdfAnnotations()[0].sdf_file, "timing.sdf");
  EXPECT_EQ(mgr.GetSdfAnnotations()[0].scope, "top.dut");
}

// =============================================================================
// Runtime SpecifyManager tests
// =============================================================================

TEST_F(SpecifyTest, RuntimePathDelay) {
  SpecifyManager mgr;
  PathDelay pd;
  pd.src_port = "a";
  pd.dst_port = "b";
  pd.rise_delay = 10;
  pd.fall_delay = 12;
  mgr.AddPathDelay(pd);

  EXPECT_TRUE(mgr.HasPathDelay("a", "b"));
  EXPECT_FALSE(mgr.HasPathDelay("b", "a"));
  EXPECT_EQ(mgr.GetPathDelay("a", "b"), 10u);
  EXPECT_EQ(mgr.GetPathDelay("x", "y"), 0u);
  EXPECT_EQ(mgr.PathDelayCount(), 1u);
}

TEST_F(SpecifyTest, RuntimeTimingCheckSetupViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetup;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = 10;
  mgr.AddTimingCheck(tc);

  // data_time=95, ref_time=100: gap=5 < 10 => violation
  EXPECT_TRUE(mgr.CheckSetupViolation("clk", 100, "data", 95));
  // data_time=85, ref_time=100: gap=15 >= 10 => no violation
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 85));
}

TEST_F(SpecifyTest, RuntimeTimingCheckHoldViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kHold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = 5;
  mgr.AddTimingCheck(tc);

  // ref_time=100, data_time=103: gap=3 < 5 => violation
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 103));
  // ref_time=100, data_time=110: gap=10 >= 5 => no violation
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 110));
}

TEST_F(SpecifyTest, RuntimeMultiplePathDelays) {
  SpecifyManager mgr;
  PathDelay pd1;
  pd1.src_port = "in1";
  pd1.dst_port = "out1";
  pd1.rise_delay = 5;
  mgr.AddPathDelay(pd1);

  PathDelay pd2;
  pd2.src_port = "in2";
  pd2.dst_port = "out2";
  pd2.rise_delay = 8;
  pd2.path_kind = SpecifyPathKind::kFull;
  mgr.AddPathDelay(pd2);

  EXPECT_EQ(mgr.PathDelayCount(), 2u);
  EXPECT_EQ(mgr.GetPathDelay("in1", "out1"), 5u);
  EXPECT_EQ(mgr.GetPathDelay("in2", "out2"), 8u);
}

}  // namespace
