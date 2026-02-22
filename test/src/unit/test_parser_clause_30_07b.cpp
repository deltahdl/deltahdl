// §30.7: Detailed control of pulse filtering behavior

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
// §30.4 Pulsestyle and showcancelled
// =============================================================================
TEST_F(SpecifyTest, PulsestyleOnevent) {
  auto *cu = Parse(
      "module m;\n"
      "specify\n"
      "  pulsestyle_onevent out1;\n"
      "endspecify\n"
      "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto *item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_FALSE(item->is_ondetect);
  ASSERT_EQ(item->signal_list.size(), 1u);
  EXPECT_EQ(item->signal_list[0], "out1");
}

TEST_F(SpecifyTest, PulsestyleOndetect) {
  auto *cu = Parse(
      "module m;\n"
      "specify\n"
      "  pulsestyle_ondetect out1;\n"
      "endspecify\n"
      "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_TRUE(spec->specify_items[0]->is_ondetect);
}

TEST_F(SpecifyTest, Showcancelled) {
  auto *cu = Parse(
      "module m;\n"
      "specify\n"
      "  showcancelled out1;\n"
      "endspecify\n"
      "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto *item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_FALSE(item->is_noshowcancelled);
}

TEST_F(SpecifyTest, Noshowcancelled) {
  auto *cu = Parse(
      "module m;\n"
      "specify\n"
      "  noshowcancelled out1;\n"
      "endspecify\n"
      "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_TRUE(spec->specify_items[0]->is_noshowcancelled);
}

}  // namespace
