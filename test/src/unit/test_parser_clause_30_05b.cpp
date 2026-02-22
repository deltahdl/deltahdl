// §30.5: Assigning delays to module paths

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

TEST_F(SpecifyTest, PathDelayWithRiseFall) {
  auto *cu = Parse("module m;\n"
                   "specify\n"
                   "  (a => b) = (3, 5);\n"
                   "endspecify\n"
                   "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto &delays = spec->specify_items[0]->path.delays;
  EXPECT_EQ(delays.size(), 2u);
}

TEST_F(SpecifyTest, PathDelayThreeValues) {
  auto *cu = Parse("module m;\n"
                   "specify\n"
                   "  (a => b) = (2, 3, 4);\n"
                   "endspecify\n"
                   "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items[0]->path.delays.size(), 3u);
}

// =============================================================================
// §30.3.3 Conditional path delays
// =============================================================================
TEST_F(SpecifyTest, ConditionalIfPath) {
  auto *cu = Parse("module m;\n"
                   "specify\n"
                   "  if (sel) (a => b) = 5;\n"
                   "endspecify\n"
                   "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto *path = spec->specify_items[0];
  EXPECT_EQ(path->kind, SpecifyItemKind::kPathDecl);
  EXPECT_NE(path->path.condition, nullptr);
  EXPECT_FALSE(path->path.is_ifnone);
}

TEST_F(SpecifyTest, IfnoneConditionalPath) {
  auto *cu = Parse("module m;\n"
                   "specify\n"
                   "  ifnone (a => b) = 7;\n"
                   "endspecify\n"
                   "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_TRUE(spec->specify_items[0]->path.is_ifnone);
  EXPECT_EQ(spec->specify_items[0]->path.condition, nullptr);
}

} // namespace
