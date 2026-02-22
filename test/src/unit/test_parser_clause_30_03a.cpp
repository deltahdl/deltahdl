// Tests for §30.3 — Specify block structure

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
  CompilationUnit *Parse(const std::string &src) {
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

TEST_F(SpecifyParseTest, EmptySpecifyBlock) {
  auto *unit = Parse("module m; specify endspecify endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kSpecifyBlock);
}

TEST_F(SpecifyParseTest, SpecifyBlockWithTimingCheck) {
  auto *unit =
      Parse("module m; specify $setup(data, posedge clk, 10); endspecify "
            "endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kSpecifyBlock);
}

TEST_F(SpecifyParseTest, SpecifyBlockCoexistsWithOtherItems) {
  auto *unit =
      Parse("module m; logic a; specify endspecify assign a = 1; endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kSpecifyBlock);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kContAssign);
}

} // namespace
