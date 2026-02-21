// Tests for §30.2 — Specparam declarations

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct SpecifyParseTest : ::testing::Test {
 protected:
  CompilationUnit* Parse(const std::string& src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

TEST_F(SpecifyParseTest, SpecparamDeclaration) {
  auto* unit = Parse("module m; specparam tRISE = 10; endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kSpecparam);
  EXPECT_EQ(items[0]->name, "tRISE");
}

TEST_F(SpecifyParseTest, SpecparamWithRange) {
  auto* unit = Parse("module m; specparam [31:0] tDELAY = 100; endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kSpecparam);
  EXPECT_EQ(items[0]->name, "tDELAY");
}

TEST_F(SpecifyParseTest, MultipleSpecparams) {
  auto* unit =
      Parse("module m; specparam tRISE = 10; specparam tFALL = 12; endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kSpecparam);
  EXPECT_EQ(items[0]->name, "tRISE");
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kSpecparam);
  EXPECT_EQ(items[1]->name, "tFALL");
}

}  // namespace
