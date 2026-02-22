// §31.4: Timing checks for clock and control signals

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/specify.h"

using namespace delta;

// =============================================================================
// Parser test fixture
// =============================================================================
struct SpecifyTest : ::testing::Test {
 protected:
  CompilationUnit *Parse(const std::string &src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  // Helper: get first specify block from first module.
  ModuleItem *FirstSpecifyBlock(CompilationUnit *cu) {
    for (auto *item : cu->modules[0]->items) {
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

namespace {

TEST_F(SpecifyTest, WidthTimingCheck) {
  auto *cu = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge clk, 20);\n"
      "endspecify\n"
      "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto &tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kWidth);
  EXPECT_EQ(tc.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.ref_terminal.name, "clk");
  ASSERT_GE(tc.limits.size(), 1u);
}

TEST_F(SpecifyTest, PeriodTimingCheck) {
  auto *cu = Parse(
      "module m;\n"
      "specify\n"
      "  $period(posedge clk, 50);\n"
      "endspecify\n"
      "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(spec->specify_items[0]->timing_check.check_kind,
            TimingCheckKind::kPeriod);
}

TEST_F(SpecifyTest, SkewTimingCheck) {
  auto *cu = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(posedge clk1, negedge clk2, 3);\n"
      "endspecify\n"
      "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto &tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kSkew);
  EXPECT_EQ(tc.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.ref_terminal.name, "clk1");
  EXPECT_EQ(tc.data_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(tc.data_terminal.name, "clk2");
}

TEST_F(SpecifyTest, NochangeTimingCheck) {
  auto *cu = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(posedge clk, data, 0, 0);\n"
      "endspecify\n"
      "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto &tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kNochange);
  ASSERT_GE(tc.limits.size(), 2u);
}

TEST_F(SpecifyTest, TimeskewTimingCheck) {
  auto *cu = Parse(
      "module m;\n"
      "specify\n"
      "  $timeskew(posedge clk1, posedge clk2, 5);\n"
      "endspecify\n"
      "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto &tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kTimeskew);
  EXPECT_EQ(tc.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.ref_terminal.name, "clk1");
  EXPECT_EQ(tc.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.data_terminal.name, "clk2");
  ASSERT_EQ(tc.limits.size(), 1u);
}

TEST_F(SpecifyTest, FullskewTimingCheck) {
  auto *cu = Parse(
      "module m;\n"
      "specify\n"
      "  $fullskew(posedge clk1, negedge clk2, 4, 6);\n"
      "endspecify\n"
      "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto &tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kFullskew);
  EXPECT_EQ(tc.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.data_edge, SpecifyEdge::kNegedge);
  ASSERT_GE(tc.limits.size(), 2u);
}

}  // namespace
