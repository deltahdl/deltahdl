// §17.8: Functions in checkers

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

static bool HasItemOfKind(const std::vector<ModuleItem *> &items,
                          ModuleItemKind kind) {
  for (const auto *item : items) {
    if (item->kind == kind) return true;
  }
  return false;
}

namespace {

// =============================================================================
// §17.10 Checker with function/task declarations
// =============================================================================
TEST_F(CheckerParseTest, CheckerWithFunctionDecl) {
  auto *unit = Parse(R"(
    checker func_check;
      function int get_val;
        return 42;
      endfunction
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(unit->checkers[0]->items, ModuleItemKind::kFunctionDecl));
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

// Returns true if any item in the list matches the given kind.
bool HasItemKind(const std::vector<ModuleItem *> &items, ModuleItemKind kind) {
  for (auto *item : items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// Returns true if any item matches the given kind and name.
bool HasItemKindNamed(const std::vector<ModuleItem *> &items,
                      ModuleItemKind kind, std::string_view name) {
  for (auto *item : items) {
    if (item->kind == kind && item->name == name) return true;
  }
  return false;
}

// checker_or_generate_item_declaration ::= function_declaration
TEST(SourceText, CheckerFunctionDecl) {
  auto r = Parse(
      "checker chk;\n"
      "  function automatic int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->name, "add");
}

}  // namespace
