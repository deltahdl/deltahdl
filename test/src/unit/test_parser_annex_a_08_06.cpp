// Tests for A.8.6 — Operators — Parser

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

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

static Expr *FirstInitialRHS(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0]->rhs;
    }
    return item->body ? item->body->rhs : nullptr;
  }
  return nullptr;
}

static Expr *FirstInitialExpr(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr
                                        : item->body->stmts[0]->expr;
    }
    return item->body ? item->body->expr : nullptr;
  }
  return nullptr;
}

}  // namespace

// =============================================================================
// A.8.6 Operators — unary_operator
// =============================================================================

// § unary_operator ::= +

TEST(ParserA86, UnaryPlus) {
  auto r = Parse("module m; initial x = +a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}

// § unary_operator ::= -

TEST(ParserA86, UnaryMinus) {
  auto r = Parse("module m; initial x = -a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kMinus);
}

// § unary_operator ::= !

TEST(ParserA86, UnaryLogicalNot) {
  auto r = Parse("module m; initial x = !a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kBang);
}

// § unary_operator ::= ~

TEST(ParserA86, UnaryBitwiseNot) {
  auto r = Parse("module m; initial x = ~a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
}

// § unary_operator ::= &

TEST(ParserA86, UnaryReductionAnd) {
  auto r = Parse("module m; initial x = &a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

// § unary_operator ::= ~&

TEST(ParserA86, UnaryReductionNand) {
  auto r = Parse("module m; initial x = ~&a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTildeAmp);
}

// § unary_operator ::= |

TEST(ParserA86, UnaryReductionOr) {
  auto r = Parse("module m; initial x = |a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
}

// § unary_operator ::= ~|

TEST(ParserA86, UnaryReductionNor) {
  auto r = Parse("module m; initial x = ~|a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTildePipe);
}

// § unary_operator ::= ^

TEST(ParserA86, UnaryReductionXor) {
  auto r = Parse("module m; initial x = ^a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kCaret);
}

// § unary_operator ::= ~^

TEST(ParserA86, UnaryReductionXnor) {
  auto r = Parse("module m; initial x = ~^a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTildeCaret);
}

// § unary_operator ::= ^~

TEST(ParserA86, UnaryReductionXnorAlt) {
  auto r = Parse("module m; initial x = ^~a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kCaretTilde);
}

// =============================================================================
// A.8.6 Operators — binary_operator (arithmetic)
// =============================================================================

// § binary_operator ::= +

TEST(ParserA86, BinaryAdd) {
  auto r = Parse("module m; initial x = a + b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}

// § binary_operator ::= -

TEST(ParserA86, BinarySub) {
  auto r = Parse("module m; initial x = a - b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kMinus);
}

// § binary_operator ::= *

TEST(ParserA86, BinaryMul) {
  auto r = Parse("module m; initial x = a * b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
}

// § binary_operator ::= /

TEST(ParserA86, BinaryDiv) {
  auto r = Parse("module m; initial x = a / b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kSlash);
}

// § binary_operator ::= %

TEST(ParserA86, BinaryMod) {
  auto r = Parse("module m; initial x = a % b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPercent);
}

// § binary_operator ::= **

TEST(ParserA86, BinaryPower) {
  auto r = Parse("module m; initial x = a ** b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPower);
}

// =============================================================================
// A.8.6 Operators — binary_operator (equality)
// =============================================================================

// § binary_operator ::= ==

TEST(ParserA86, BinaryEq) {
  auto r = Parse("module m; initial x = (a == b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEq);
}

// § binary_operator ::= !=

TEST(ParserA86, BinaryNeq) {
  auto r = Parse("module m; initial x = (a != b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kBangEq);
}

// § binary_operator ::= ===

TEST(ParserA86, BinaryCaseEq) {
  auto r = Parse("module m; initial x = (a === b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEqEq);
}

// § binary_operator ::= !==

TEST(ParserA86, BinaryCaseNeq) {
  auto r = Parse("module m; initial x = (a !== b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kBangEqEq);
}

// § binary_operator ::= ==?

TEST(ParserA86, BinaryWildcardEq) {
  auto r = Parse("module m; initial x = (a ==? b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEqQuestion);
}

// § binary_operator ::= !=?

TEST(ParserA86, BinaryWildcardNeq) {
  auto r = Parse("module m; initial x = (a !=? b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kBangEqQuestion);
}

// =============================================================================
// A.8.6 Operators — binary_operator (logical)
// =============================================================================

// § binary_operator ::= &&

TEST(ParserA86, BinaryLogicalAnd) {
  auto r = Parse("module m; initial x = (a && b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
}

// § binary_operator ::= ||

TEST(ParserA86, BinaryLogicalOr) {
  auto r = Parse("module m; initial x = (a || b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPipePipe);
}

// =============================================================================
// A.8.6 Operators — binary_operator (relational)
// =============================================================================

// § binary_operator ::= <

TEST(ParserA86, BinaryLessThan) {
  auto r = Parse("module m; initial x = (a < b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLt);
}

// § binary_operator ::= <=

TEST(ParserA86, BinaryLessOrEqual) {
  auto r = Parse("module m; initial x = (a <= b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtEq);
}

// § binary_operator ::= >

TEST(ParserA86, BinaryGreaterThan) {
  auto r = Parse("module m; initial x = (a > b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kGt);
}

// § binary_operator ::= >=

TEST(ParserA86, BinaryGreaterOrEqual) {
  auto r = Parse("module m; initial x = (a >= b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kGtEq);
}

// =============================================================================
// A.8.6 Operators — binary_operator (bitwise)
// =============================================================================

// § binary_operator ::= &

TEST(ParserA86, BinaryBitwiseAnd) {
  auto r = Parse("module m; initial x = a & b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

// § binary_operator ::= |

TEST(ParserA86, BinaryBitwiseOr) {
  auto r = Parse("module m; initial x = a | b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
}

// § binary_operator ::= ^

TEST(ParserA86, BinaryBitwiseXor) {
  auto r = Parse("module m; initial x = a ^ b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kCaret);
}

// § binary_operator ::= ^~

TEST(ParserA86, BinaryBitwiseXnor) {
  auto r = Parse("module m; initial x = a ^~ b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kCaretTilde);
}

// § binary_operator ::= ~^

TEST(ParserA86, BinaryBitwiseXnorAlt) {
  auto r = Parse("module m; initial x = a ~^ b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kTildeCaret);
}

// =============================================================================
// A.8.6 Operators — binary_operator (shift)
// =============================================================================

// § binary_operator ::= >>

TEST(ParserA86, BinaryLogicalRightShift) {
  auto r = Parse("module m; initial x = a >> 2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kGtGt);
}

// § binary_operator ::= <<

TEST(ParserA86, BinaryLogicalLeftShift) {
  auto r = Parse("module m; initial x = a << 2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtLt);
}

// § binary_operator ::= >>>

TEST(ParserA86, BinaryArithRightShift) {
  auto r = Parse("module m; initial x = a >>> 2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kGtGtGt);
}

// § binary_operator ::= <<<

TEST(ParserA86, BinaryArithLeftShift) {
  auto r = Parse("module m; initial x = a <<< 2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtLtLt);
}

// =============================================================================
// A.8.6 Operators — binary_operator (implication)
// =============================================================================

// § binary_operator ::= ->

TEST(ParserA86, BinaryImplication) {
  auto r = Parse("module m; initial x = (a -> b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kArrow);
}

// § binary_operator ::= <->

TEST(ParserA86, BinaryEquivalence) {
  auto r = Parse("module m; initial x = (a <-> b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtDashGt);
}

// =============================================================================
// A.8.6 Operators — inc_or_dec_operator
// =============================================================================

// § inc_or_dec_operator ::= ++ (prefix)

TEST(ParserA86, IncOrDecPrefixIncrement) {
  auto r = Parse("module m; initial ++x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kUnary);
  EXPECT_EQ(expr->op, TokenKind::kPlusPlus);
}

// § inc_or_dec_operator ::= -- (prefix)

TEST(ParserA86, IncOrDecPrefixDecrement) {
  auto r = Parse("module m; initial --x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kUnary);
  EXPECT_EQ(expr->op, TokenKind::kMinusMinus);
}

// § inc_or_dec_operator ::= ++ (postfix)

TEST(ParserA86, IncOrDecPostfixIncrement) {
  auto r = Parse("module m; initial x++; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(expr->op, TokenKind::kPlusPlus);
}

// § inc_or_dec_operator ::= -- (postfix)

TEST(ParserA86, IncOrDecPostfixDecrement) {
  auto r = Parse("module m; initial x--; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(expr->op, TokenKind::kMinusMinus);
}

// =============================================================================
// A.8.6 Operators — unary_module_path_operator
// =============================================================================

// § unary_module_path_operator — ! in specify path condition

TEST(ParserA86, UnaryModulePathNot) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (!a) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § unary_module_path_operator — ~ in specify path condition

TEST(ParserA86, UnaryModulePathBitwiseNot) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (~a) (a => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.6 Operators — binary_module_path_operator
// =============================================================================

// § binary_module_path_operator — == in specify path condition

TEST(ParserA86, BinaryModulePathEq) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a == b) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § binary_module_path_operator — != in specify path condition

TEST(ParserA86, BinaryModulePathNeq) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a != b) (a => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § binary_module_path_operator — && in specify path condition

TEST(ParserA86, BinaryModulePathLogicalAnd) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a && b) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § binary_module_path_operator — || in specify path condition

TEST(ParserA86, BinaryModulePathLogicalOr) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a || b) (a => y) = 4;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § binary_module_path_operator — & in specify path condition

TEST(ParserA86, BinaryModulePathBitwiseAnd) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a & b) (a => y) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § binary_module_path_operator — | in specify path condition

TEST(ParserA86, BinaryModulePathBitwiseOr) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a | b) (a => y) = 6;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § binary_module_path_operator — ^ in specify path condition

TEST(ParserA86, BinaryModulePathXor) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a ^ b) (a => y) = 7;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § binary_module_path_operator — ^~ in specify path condition

TEST(ParserA86, BinaryModulePathXnor) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a ^~ b) (a => y) = 8;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § binary_module_path_operator — ~^ in specify path condition

TEST(ParserA86, BinaryModulePathXnorAlt) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a ~^ b) (a => y) = 9;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
