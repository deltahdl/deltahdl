// §7.12.1: Array locator methods

#include "fixture_parser.h"

using namespace delta;

struct ParseResult7b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static Stmt* FirstInitialStmt(ParseResult7b& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

// --- Test helpers ---
struct ParseResult7c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult7c Parse(const std::string& src) {
  ParseResult7c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// =========================================================================
// §7.12.1: Array locator methods
// =========================================================================
TEST(ParserSection7, ArrayFindWithClause) {
  auto r = Parse(
      "module t;\n"
      "  int d[] = '{1,2,3,4,5};\n"
      "  initial qi = d.find with (item > 3);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
}

TEST(ParserSection7, ArrayFindIndexMethod) {
  auto r = Parse(
      "module t;\n"
      "  int arr[8];\n"
      "  initial qi = arr.find_index with (item == 0);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

// =========================================================================
// §7.12.1: Array locator method 'unique' (keyword as method name)
// =========================================================================
TEST(ParserSection7, ArrayLocatorUnique) {
  auto r = Parse(
      "module t;\n"
      "  int s[] = '{10, 10, 3, 20, 20, 10};\n"
      "  int qi[$];\n"
      "  initial qi = s.unique;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

// =========================================================================
// §7.12: Array manipulation methods (additional tests)
// =========================================================================
TEST(ParserSection7, ArrayLocatorFindWithClause) {
  auto r = Parse(
      "module t;\n"
      "  int arr[] = '{1, 2, 3, 4, 5};\n"
      "  int found[$];\n"
      "  initial found = arr.find with (item > 3);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}

}  // namespace
