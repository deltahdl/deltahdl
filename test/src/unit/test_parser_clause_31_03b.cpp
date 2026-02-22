// §31.3: Timing checks using a stability window

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

// =============================================================================
// §31 Timing checks
// =============================================================================
TEST_F(SpecifyTest, SetupTimingCheck) {
  auto *cu = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto &tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(tc.ref_terminal.name, "data");
  EXPECT_EQ(tc.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.data_terminal.name, "clk");
  ASSERT_EQ(tc.limits.size(), 1u);
}

TEST_F(SpecifyTest, HoldTimingCheck) {
  auto *cu = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk, data, 5);\n"
      "endspecify\n"
      "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto &tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kHold);
  EXPECT_EQ(tc.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.ref_terminal.name, "clk");
  EXPECT_EQ(tc.data_terminal.name, "data");
}

TEST_F(SpecifyTest, SetupholdTimingCheck) {
  auto *cu = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5);\n"
      "endspecify\n"
      "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto &tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kSetuphold);
  ASSERT_GE(tc.limits.size(), 2u);
}

TEST_F(SpecifyTest, RecoveryTimingCheck) {
  auto *cu = Parse(
      "module m;\n"
      "specify\n"
      "  $recovery(posedge clk, rst, 8);\n"
      "endspecify\n"
      "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(spec->specify_items[0]->timing_check.check_kind,
            TimingCheckKind::kRecovery);
}

TEST_F(SpecifyTest, RemovalTimingCheck) {
  auto *cu = Parse(
      "module m;\n"
      "specify\n"
      "  $removal(posedge clk, rst, 3);\n"
      "endspecify\n"
      "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(spec->specify_items[0]->timing_check.check_kind,
            TimingCheckKind::kRemoval);
}

TEST_F(SpecifyTest, RecremTimingCheck) {
  auto *cu = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge clk, rst, 8, 3);\n"
      "endspecify\n"
      "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto &tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kRecrem);
  ASSERT_GE(tc.limits.size(), 2u);
}

}  // namespace
