// §11.4.7: Logical operators

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.8.6 Operators — binary_operator (logical)
// =============================================================================
// § binary_operator ::= &&
TEST(ParserA86, BinaryLogicalAnd) {
  auto r = Parse("module m; initial x = (a && b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
}

// § binary_operator ::= ||
TEST(ParserA86, BinaryLogicalOr) {
  auto r = Parse("module m; initial x = (a || b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPipePipe);
}

// =============================================================================
// A.8.6 Operators — binary_operator (implication)
// =============================================================================
// § binary_operator ::= ->
TEST(ParserA86, BinaryImplication) {
  auto r = Parse("module m; initial x = (a -> b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kArrow);
}

// § binary_operator ::= <->
TEST(ParserA86, BinaryEquivalence) {
  auto r = Parse("module m; initial x = (a <-> b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtDashGt);
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

// --- Logical implication and equivalence (§11.4.7) ---
TEST(ParserSection11, ImplicationParsed) {
  auto r = Parse(
      "module t;\n"
      "  logic a, b, c;\n"
      "  initial c = a -> b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kArrow);
}

TEST(ParserSection11, EquivalenceParsed) {
  auto r = Parse(
      "module t;\n"
      "  logic a, b, c;\n"
      "  initial c = a <-> b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtDashGt);
}

TEST(ParserA83, ExprUnaryNot) {
  auto r = Parse("module m; initial x = !a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kBang);
}

TEST(ParserSection11, ImplicationRightAssocStructure) {
  // a -> b -> c should be parsed as a -> (b -> c)
  auto r = Parse(
      "module t;\n"
      "  logic a, b, c, d;\n"
      "  initial d = a -> b -> c;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  // LHS is 'a', RHS is 'b -> c'
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kArrow);
}

TEST(ParserA83, ExprBinaryLogicalAnd) {
  auto r = Parse("module m; initial x = a && b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
}

// § unary_operator ::= !
TEST(ParserA86, UnaryLogicalNot) {
  auto r = Parse("module m; initial x = !a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kBang);
}

struct ParseResult11e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11e Parse(const std::string& src) {
  ParseResult11e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult11e& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Expr* FirstAssignRhs(ParseResult11e& r) {
  auto* stmt = FirstInitialStmt(r);
  if (!stmt) return nullptr;
  return stmt->rhs;
}

TEST(ParserSection11, Sec11_1_UnaryLogicalNot) {
  auto r = Parse(
      "module t;\n"
      "  initial x = !flag;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kBang);
}

// =========================================================================
// Section 11.4.7 -- Logical operators
// =========================================================================
TEST(ParserSection11, LogicalAnd) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a && b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
}

TEST(ParserSection11, LogicalOr) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a || b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPipePipe);
}

TEST(ParserSection11, LogicalNot) {
  auto r = Parse(
      "module t;\n"
      "  initial x = !a;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kBang);
}

}  // namespace
