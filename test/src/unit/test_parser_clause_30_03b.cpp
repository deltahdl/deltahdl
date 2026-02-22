// §30.3: Specify block declaration

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

namespace {

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

}  // namespace
