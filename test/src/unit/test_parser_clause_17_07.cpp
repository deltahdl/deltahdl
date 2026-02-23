// §17.7: Checker variables

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"

using namespace delta;

// =============================================================================
// Parse-level fixture
// =============================================================================
struct CheckerParseTest : ::testing::Test {
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

// =============================================================================
// Elaboration fixture
// =============================================================================
struct CheckerElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

namespace {

// =============================================================================
// §17.4 Checker variables
// =============================================================================
TEST_F(CheckerParseTest, CheckerWithVariables) {
  auto *unit = Parse(R"(
    checker var_check;
      logic a, b;
      assign a = b;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

TEST_F(CheckerParseTest, CheckerWithBitVector) {
  auto *unit = Parse(R"(
    checker bv_check;
      logic [7:0] counter;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

// --- Test helpers ---
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// checker_or_generate_item_declaration ::= [rand] data_declaration
TEST(SourceText, CheckerRandDataDecl) {
  auto r = Parse(
      "checker chk;\n"
      "  rand bit [3:0] val;\n"
      "  logic [7:0] data;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->items.size(), 2u);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_TRUE(r.cu->checkers[0]->items[0]->is_rand);
  EXPECT_EQ(r.cu->checkers[0]->items[1]->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(r.cu->checkers[0]->items[1]->is_rand);
}

}  // namespace
