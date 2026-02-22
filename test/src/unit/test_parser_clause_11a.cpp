#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult11 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult11 Parse(const std::string &src) {
  ParseResult11 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt *FirstInitialStmt(ParseResult11 &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock)
      continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

// Helper: get the RHS of the first blocking assignment in initial block.
static Expr *FirstAssignRhs(ParseResult11 &r) {
  auto *stmt = FirstInitialStmt(r);
  if (!stmt)
    return nullptr;
  return stmt->rhs;
}

// =========================================================================
// Section 11.3.6 -- Assignment operators in expressions
// =========================================================================

TEST(ParserSection11, CompoundAssignPlusEq) {
  auto r = Parse("module t;\n"
                 "  initial a += 1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  // Compound assignment is parsed as blocking assign with op
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection11, CompoundAssignMinusEq) {
  auto r = Parse("module t;\n"
                 "  initial a -= 1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection11, CompoundAssignStarEq) {
  auto r = Parse("module t;\n"
                 "  initial a *= 2;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignSlashEq) {
  auto r = Parse("module t;\n"
                 "  initial a /= 2;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignPercentEq) {
  auto r = Parse("module t;\n"
                 "  initial a %= 3;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignAmpEq) {
  auto r = Parse("module t;\n"
                 "  initial a &= 8'hFF;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignPipeEq) {
  auto r = Parse("module t;\n"
                 "  initial a |= 8'h0F;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignCaretEq) {
  auto r = Parse("module t;\n"
                 "  initial a ^= b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignLtLtEq) {
  auto r = Parse("module t;\n"
                 "  initial a <<= 2;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignGtGtEq) {
  auto r = Parse("module t;\n"
                 "  initial a >>= 2;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignLtLtLtEq) {
  auto r = Parse("module t;\n"
                 "  initial a <<<= 1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignGtGtGtEq) {
  auto r = Parse("module t;\n"
                 "  initial a >>>= 1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =========================================================================
// Section 11.4.2 -- Increment/decrement operators
// =========================================================================

TEST(ParserSection11, PrefixIncrement) {
  auto r = Parse("module t;\n"
                 "  initial ++a;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, PrefixDecrement) {
  auto r = Parse("module t;\n"
                 "  initial --a;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, PostfixIncrementParses) {
  auto r = Parse("module t;\n"
                 "  initial a++;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(ParserSection11, PostfixIncrementOp) {
  auto r = Parse("module t;\n"
                 "  initial a++;\n"
                 "endmodule\n");
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(stmt->expr->op, TokenKind::kPlusPlus);
}

TEST(ParserSection11, PostfixDecrementParses) {
  auto r = Parse("module t;\n"
                 "  initial a--;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(ParserSection11, PostfixDecrementOp) {
  auto r = Parse("module t;\n"
                 "  initial a--;\n"
                 "endmodule\n");
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(stmt->expr->op, TokenKind::kMinusMinus);
}

// =========================================================================
// Section 11.4.13 -- Inside operator (set membership)
// =========================================================================

TEST(ParserSection11, InsideBasicListParses) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    if (a inside {1, 2, 3}) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
}

TEST(ParserSection11, InsideBasicListCondition) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    if (a inside {1, 2, 3}) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->kind, ExprKind::kInside);
  EXPECT_EQ(cond->elements.size(), 3u);
}

TEST(ParserSection11, InsideBasicListLhs) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    if (a inside {1, 2, 3}) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  ASSERT_NE(cond->lhs, nullptr);
  EXPECT_EQ(cond->lhs->kind, ExprKind::kIdentifier);
}

TEST(ParserSection11, InsideWithRange) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    if (a inside {[16:23], [32:47]}) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->kind, ExprKind::kInside);
}

TEST(ParserSection11, InsideWithRangeElements) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    if (a inside {[16:23], [32:47]}) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->elements.size(), 2u);
}

TEST(ParserSection11, InsideInAssign) {
  auto r = Parse("module t;\n"
                 "  wire r;\n"
                 "  assign r = a inside {1, 2, 3};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =========================================================================
// Section 11.4.14 -- Streaming operators
// =========================================================================

TEST(ParserSection11, StreamingRight) {
  auto r = Parse("module t;\n"
                 "  initial x = {>> {a, b, c}};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
}

TEST(ParserSection11, StreamingRightDetails) {
  auto r = Parse("module t;\n"
                 "  initial x = {>> {a, b, c}};\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kGtGt);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

TEST(ParserSection11, StreamingLeft) {
  auto r = Parse("module t;\n"
                 "  initial x = {<< {a, b, c}};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(rhs->op, TokenKind::kLtLt);
}

TEST(ParserSection11, StreamingWithSliceSize) {
  auto r = Parse("module t;\n"
                 "  initial x = {<< 8 {a, b}};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_NE(rhs->lhs, nullptr); // slice_size
}

// =========================================================================
// Section 11.11 -- Min/typ/max delay expressions
// =========================================================================

TEST(ParserSection11, MinTypMaxInDelay) {
  auto r = Parse("module t;\n"
                 "  initial #(1:2:3) x = 1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, MinTypMaxInContAssign) {
  auto r = Parse("module t;\n"
                 "  wire a;\n"
                 "  assign #(1:2:3) a = 1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =========================================================================
// Section 11.4.10 -- Arithmetic shift operators
// =========================================================================

TEST(ParserSection11, ArithmeticShiftLeft) {
  auto r = Parse("module t;\n"
                 "  initial x = a <<< 2;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtLtLt);
}

TEST(ParserSection11, ArithmeticShiftRight) {
  auto r = Parse("module t;\n"
                 "  initial x = a >>> 2;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kGtGtGt);
}

// =========================================================================
// Compound assignment operators within expressions (parenthesized)
// =========================================================================

TEST(ParserSection11, AssignInExprParenthesized) {
  auto r = Parse("module t;\n"
                 "  initial if ((a = b)) x = 1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignInExpr) {
  auto r = Parse("module t;\n"
                 "  initial b = (a += 1);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =========================================================================
// Postfix increment in for-loop step
// =========================================================================

TEST(ParserSection11, PostfixIncrementInForStep) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 10; i++)\n"
                 "      x = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, PrefixDecrementInForStep) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    for (int i = 10; i > 0; --i)\n"
                 "      x = i;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =========================================================================
// Section 11.4.3 -- Arithmetic operators
// =========================================================================

TEST(ParserSection11, ArithmeticAdd) {
  auto r = Parse("module t;\n"
                 "  initial x = a + b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}

TEST(ParserSection11, ArithmeticSub) {
  auto r = Parse("module t;\n"
                 "  initial x = a - b;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kMinus);
}

TEST(ParserSection11, ArithmeticMul) {
  auto r = Parse("module t;\n"
                 "  initial x = a * b;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
}

TEST(ParserSection11, ArithmeticDiv) {
  auto r = Parse("module t;\n"
                 "  initial x = a / b;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kSlash);
}

TEST(ParserSection11, ArithmeticMod) {
  auto r = Parse("module t;\n"
                 "  initial x = a % b;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPercent);
}

TEST(ParserSection11, ArithmeticPower) {
  auto r = Parse("module t;\n"
                 "  initial x = a ** b;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPower);
}

TEST(ParserSection11, UnaryNegation) {
  auto r = Parse("module t;\n"
                 "  initial x = -a;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kMinus);
}
