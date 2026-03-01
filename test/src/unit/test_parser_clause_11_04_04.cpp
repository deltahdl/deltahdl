// §11.4.4: Relational operators

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.8.6 Operators — binary_operator (relational)
// =============================================================================
// § binary_operator ::= <
TEST(ParserA86, BinaryLessThan) {
  auto r = Parse("module m; initial x = (a < b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLt);
}

// § binary_operator ::= <=
TEST(ParserA86, BinaryLessOrEqual) {
  auto r = Parse("module m; initial x = (a <= b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtEq);
}

// § binary_operator ::= >
TEST(ParserA86, BinaryGreaterThan) {
  auto r = Parse("module m; initial x = (a > b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kGt);
}

// § binary_operator ::= >=
TEST(ParserA86, BinaryGreaterOrEqual) {
  auto r = Parse("module m; initial x = (a >= b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kGtEq);
}

struct ParseResult11d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11d Parse(const std::string& src) {
  ParseResult11d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult11d& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Expr* FirstAssignRhs(ParseResult11d& r) {
  auto* stmt = FirstInitialStmt(r);
  if (!stmt) return nullptr;
  return stmt->rhs;
}

// =========================================================================
// Section 11.4.4 -- Relational operators
// =========================================================================
TEST(ParserSection11, RelationalLt) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a < b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kLt);
}

TEST(ParserSection11, RelationalGt) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a > b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kGt);
}

TEST(ParserSection11, RelationalLtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a <= b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kLtEq);
}

TEST(ParserSection11, RelationalGtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a >= b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kGtEq);
}

}  // namespace
