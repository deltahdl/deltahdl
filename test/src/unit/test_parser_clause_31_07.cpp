// §31.7: Enabling timing checks with conditioned events

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/specify.h"
#include <gtest/gtest.h>

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
      if (item->kind == ModuleItemKind::kSpecifyBlock)
        return item;
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
// §31.7 Conditioned events
// =============================================================================
TEST_F(SpecifyTest, ConditionedSetup) {
  auto *cu = Parse("module m;\n"
                   "specify\n"
                   "  $setup(data &&& clr, posedge clk, 10);\n"
                   "endspecify\n"
                   "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto &tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(tc.ref_terminal.name, "data");
  EXPECT_NE(tc.ref_condition, nullptr);
}

TEST_F(SpecifyTest, ConditionedHoldBothSignals) {
  auto *cu = Parse("module m;\n"
                   "specify\n"
                   "  $hold(posedge clk &&& en, data &&& reset, 5);\n"
                   "endspecify\n"
                   "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto &tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kHold);
  EXPECT_NE(tc.ref_condition, nullptr);
  EXPECT_NE(tc.data_condition, nullptr);
}

} // namespace
