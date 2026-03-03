// §11.4.9: Reduction operators

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

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

namespace {

TEST(ParserSection11, ReductionOnParenthesizedExpr) {
  auto r = Parse(
      "module t;\n"
      "  initial x = &(a ^ b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

// Unary reduction operators
TEST(ParserA83, UnaryReductionAnd) {
  auto r = Parse("module m; initial x = &a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

TEST(ParserA83, UnaryReductionOr) {
  auto r = Parse("module m; initial x = |a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
}

TEST(ParserA83, UnaryReductionXor) {
  auto r = Parse("module m; initial x = ^a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kCaret);
}

// § unary_operator ::= ~&
TEST(ParserA86, UnaryReductionNand) {
  auto r = Parse("module m; initial x = ~&a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTildeAmp);
}

// § unary_operator ::= ~|
TEST(ParserA86, UnaryReductionNor) {
  auto r = Parse("module m; initial x = ~|a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTildePipe);
}

// § unary_operator ::= ~^
TEST(ParserA86, UnaryReductionXnor) {
  auto r = Parse("module m; initial x = ~^a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTildeCaret);
}

// § unary_operator ::= ^~
TEST(ParserA86, UnaryReductionXnorAlt) {
  auto r = Parse("module m; initial x = ^~a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kCaretTilde);
}

// =========================================================================
// Section 11.4.3.1 -- Unary reduction operators
// =========================================================================
TEST(ParserSection11, ReductionXnorCaretTilde) {
  auto r = Parse(
      "module t;\n"
      "  initial x = ^~a;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kCaretTilde);
}

TEST(ParserSection11, Sec11_1_UnaryReductionNand) {
  auto r = Parse(
      "module t;\n"
      "  initial x = ~&data;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTildeAmp);
}

TEST(ParserSection11, Sec11_1_UnaryReductionNor) {
  auto r = Parse(
      "module t;\n"
      "  initial x = ~|data;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTildePipe);
}

TEST(ParserSection11, Sec11_1_UnaryReductionXnorTildeCaret) {
  auto r = Parse(
      "module t;\n"
      "  initial x = ~^data;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTildeCaret);
}

TEST(ParserSection11, Sec11_1_UnaryReductionXnorCaretTilde) {
  auto r = Parse(
      "module t;\n"
      "  initial x = ^~data;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kCaretTilde);
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
// Section 11.4.9 -- Reduction operators
// =========================================================================
TEST(ParserSection11, ReductionAnd) {
  auto r = Parse(
      "module t;\n"
      "  initial x = &a;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

TEST(ParserSection11, ReductionOr) {
  auto r = Parse(
      "module t;\n"
      "  initial x = |a;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
}

TEST(ParserSection11, ReductionXor) {
  auto r = Parse(
      "module t;\n"
      "  initial x = ^a;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kCaret);
}

}  // namespace
