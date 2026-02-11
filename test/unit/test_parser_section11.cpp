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
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11 Parse(const std::string& src) {
  ParseResult11 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult11& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

// Helper: get the RHS of the first blocking assignment in initial block.
static Expr* FirstAssignRhs(ParseResult11& r) {
  auto* stmt = FirstInitialStmt(r);
  if (!stmt) return nullptr;
  return stmt->rhs;
}

// =========================================================================
// Section 11.3.6 -- Assignment operators in expressions
// =========================================================================

TEST(ParserSection11, CompoundAssignPlusEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a += 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  // Compound assignment is parsed as blocking assign with op
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection11, CompoundAssignMinusEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a -= 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection11, CompoundAssignStarEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a *= 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignSlashEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a /= 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignPercentEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a %= 3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignAmpEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a &= 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignPipeEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a |= 8'h0F;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignCaretEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a ^= b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignLtLtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a <<= 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignGtGtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a >>= 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignLtLtLtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a <<<= 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignGtGtGtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a >>>= 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =========================================================================
// Section 11.4.2 -- Increment/decrement operators
// =========================================================================

TEST(ParserSection11, PrefixIncrement) {
  auto r = Parse(
      "module t;\n"
      "  initial ++a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, PrefixDecrement) {
  auto r = Parse(
      "module t;\n"
      "  initial --a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, PostfixIncrement) {
  auto r = Parse(
      "module t;\n"
      "  initial a++;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(stmt->expr->op, TokenKind::kPlusPlus);
}

TEST(ParserSection11, PostfixDecrement) {
  auto r = Parse(
      "module t;\n"
      "  initial a--;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(stmt->expr->op, TokenKind::kMinusMinus);
}

// =========================================================================
// Section 11.4.13 -- Inside operator (set membership)
// =========================================================================

TEST(ParserSection11, InsideBasicList) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a inside {1, 2, 3}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  auto* cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->kind, ExprKind::kInside);
  ASSERT_NE(cond->lhs, nullptr);
  EXPECT_EQ(cond->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(cond->elements.size(), 3u);
}

TEST(ParserSection11, InsideWithRange) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a inside {[16:23], [32:47]}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* cond = stmt->condition;
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(cond->kind, ExprKind::kInside);
  EXPECT_EQ(cond->elements.size(), 2u);
}

TEST(ParserSection11, InsideInAssign) {
  auto r = Parse(
      "module t;\n"
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
  auto r = Parse(
      "module t;\n"
      "  initial x = {>> {a, b, c}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(rhs->op, TokenKind::kGtGt);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

TEST(ParserSection11, StreamingLeft) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {<< {a, b, c}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(rhs->op, TokenKind::kLtLt);
}

TEST(ParserSection11, StreamingWithSliceSize) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {<< 8 {a, b}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_NE(rhs->lhs, nullptr);  // slice_size
}

// =========================================================================
// Section 11.11 -- Min/typ/max delay expressions
// =========================================================================

TEST(ParserSection11, MinTypMaxInDelay) {
  auto r = Parse(
      "module t;\n"
      "  initial #(1:2:3) x = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, MinTypMaxInContAssign) {
  auto r = Parse(
      "module t;\n"
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
  auto r = Parse(
      "module t;\n"
      "  initial x = a <<< 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtLtLt);
}

TEST(ParserSection11, ArithmeticShiftRight) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a >>> 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kGtGtGt);
}

// =========================================================================
// Compound assignment operators within expressions (parenthesized)
// =========================================================================

TEST(ParserSection11, AssignInExprParenthesized) {
  auto r = Parse(
      "module t;\n"
      "  initial if ((a = b)) x = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignInExpr) {
  auto r = Parse(
      "module t;\n"
      "  initial b = (a += 1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =========================================================================
// Postfix increment in for-loop step
// =========================================================================

TEST(ParserSection11, PostfixIncrementInForStep) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++)\n"
      "      x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, PrefixDecrementInForStep) {
  auto r = Parse(
      "module t;\n"
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
  auto r = Parse(
      "module t;\n"
      "  initial x = a + b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}

TEST(ParserSection11, ArithmeticSub) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a - b;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kMinus);
}

TEST(ParserSection11, ArithmeticMul) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a * b;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
}

TEST(ParserSection11, ArithmeticDiv) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a / b;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kSlash);
}

TEST(ParserSection11, ArithmeticMod) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a % b;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPercent);
}

TEST(ParserSection11, ArithmeticPower) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a ** b;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPower);
}

TEST(ParserSection11, UnaryNegation) {
  auto r = Parse(
      "module t;\n"
      "  initial x = -a;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kMinus);
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

// =========================================================================
// Section 11.4.5 -- Equality operators
// =========================================================================

TEST(ParserSection11, EqualityEq) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a == b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kEqEq);
}

TEST(ParserSection11, EqualityNeq) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a != b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kBangEq);
}

TEST(ParserSection11, CaseEqualityEq) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a === b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kEqEqEq);
}

TEST(ParserSection11, CaseEqualityNeq) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a !== b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kBangEqEq);
}

// =========================================================================
// Section 11.4.6 -- Wildcard equality operators
// =========================================================================

TEST(ParserSection11, WildcardEq) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a ==? b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kEqEqQuestion);
}

TEST(ParserSection11, WildcardNeq) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a !=? b);\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kBangEqQuestion);
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

// =========================================================================
// Section 11.4.8 -- Bitwise operators
// =========================================================================

TEST(ParserSection11, BitwiseAnd) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a & b;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

TEST(ParserSection11, BitwiseOr) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a | b;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
}

TEST(ParserSection11, BitwiseXor) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a ^ b;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kCaret);
}

TEST(ParserSection11, BitwiseNot) {
  auto r = Parse(
      "module t;\n"
      "  initial x = ~a;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
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

TEST(ParserSection11, ReductionNand) {
  auto r = Parse(
      "module t;\n"
      "  initial x = ~&a;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTildeAmp);
}

TEST(ParserSection11, ReductionNor) {
  auto r = Parse(
      "module t;\n"
      "  initial x = ~|a;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTildePipe);
}

TEST(ParserSection11, ReductionXnor) {
  auto r = Parse(
      "module t;\n"
      "  initial x = ~^a;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTildeCaret);
}

// =========================================================================
// Section 11.4.11 -- Conditional operator
// =========================================================================

TEST(ParserSection11, ConditionalTernary) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a > b) ? a : b;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
}

// =========================================================================
// Section 11.4.12 -- Concatenation operators
// =========================================================================

TEST(ParserSection11, ConcatenationBasic) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {a, b, c};\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

TEST(ParserSection11, ReplicationOperator) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {4{a}};\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
}

// =========================================================================
// Section 11.4.10 -- Shift operators (logical)
// =========================================================================

TEST(ParserSection11, LogicalShiftLeft) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a << 2;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kLtLt);
}

TEST(ParserSection11, LogicalShiftRight) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a >> 2;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kGtGt);
}

// =========================================================================
// Section 11.3.2 -- Operator precedence (complex expression)
// =========================================================================

TEST(ParserSection11, OperatorPrecedenceMixedArith) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a + b * c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  // * has higher precedence than +, so top-level is +
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kStar);
}

TEST(ParserSection11, OperatorPrecedenceCompareAndLogical) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a > 0) && (b < 10);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
}

// =========================================================================
// Section 11.5.1 -- Bit-select and part-select
// =========================================================================

TEST(ParserSection11, BitSelect) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a[3];\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
}

TEST(ParserSection11, PartSelectConstant) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a[7:0];\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
}

// =========================================================================
// Section 11.3.5 -- Short-circuit evaluation
// =========================================================================

TEST(ParserSection11, ShortCircuitAnd) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a != 0) && (b / a > 1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =========================================================================
// Section 11.7 -- Signed expressions ($signed, $unsigned)
// =========================================================================

TEST(ParserSection11, SignedSystemCall) {
  auto r = Parse(
      "module t;\n"
      "  initial x = $signed(a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$signed");
}

TEST(ParserSection11, UnsignedSystemCall) {
  auto r = Parse(
      "module t;\n"
      "  initial x = $unsigned(a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$unsigned");
}
