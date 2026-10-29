#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

TEST(LexicalConventionParsing, TwoCharOperators) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = (a == b);\n"
              "    x = (a != b);\n"
              "    x = (a <= b);\n"
              "    x = (a >= b);\n"
              "    x = (a && b);\n"
              "    x = (a || b);\n"
              "    x = a << 1;\n"
              "    x = a >> 1;\n"
              "    a += 1;\n"
              "    a -= 1;\n"
              "    a *= 2;\n"
              "    a /= 2;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, TwoCharOperatorTokenKinds) {
  auto r = Parse(
      "module m;\n"
      "  initial x = (a == b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEq);
}

TEST(LexicalConventionParsing, ThreeCharOperators) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = (a === b);\n"
              "    x = (a !== b);\n"
              "    x = a <<< 2;\n"
              "    x = a >>> 2;\n"
              "    x = (a ==? b);\n"
              "    x = (a !=? b);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, UnaryOperatorsLeftOfOperand) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = ~a;\n"
      "    x = !a;\n"
      "    x = -a;\n"
      "    x = +a;\n"
      "    x = &a;\n"
      "    x = |a;\n"
      "    x = ^a;\n"
      "    x = ~&a;\n"
      "    x = ~|a;\n"
      "    x = ~^a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kTilde);
}

TEST(LexicalConventionParsing, UnaryPrefixIncDec) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    ++x;\n"
              "    --x;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, BinaryOperatorBetweenOperands) {
  auto r = Parse(
      "module m;\n"
      "  initial x = a + b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(LexicalConventionParsing, AllBinaryArithmeticOperators) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = a + b;\n"
              "    x = a - b;\n"
              "    x = a * b;\n"
              "    x = a / b;\n"
              "    x = a % b;\n"
              "    x = a ** b;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, AllBinaryBitwiseOperators) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = a & b;\n"
              "    x = a | b;\n"
              "    x = a ^ b;\n"
              "    x = a ~^ b;\n"
              "    x = a ^~ b;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, ConditionalOperatorThreeOperands) {
  auto r = Parse(
      "module m;\n"
      "  initial x = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  EXPECT_EQ(rhs->condition->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kIdentifier);
}

TEST(LexicalConventionParsing, NestedConditionalOperator) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial x = a ? b ? c : d : e;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, CompoundAssignmentOperators) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    a += 1;\n"
              "    a -= 1;\n"
              "    a *= 2;\n"
              "    a /= 2;\n"
              "    a %= 3;\n"
              "    a &= 8'hFF;\n"
              "    a |= 8'h0F;\n"
              "    a ^= 8'hAA;\n"
              "    a <<= 1;\n"
              "    a >>= 1;\n"
              "    a <<<= 1;\n"
              "    a >>>= 1;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, SingleCharOperatorsInExpressions) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = a + b;\n"
              "    x = a - b;\n"
              "    x = a * b;\n"
              "    x = a / b;\n"
              "    x = a % b;\n"
              "    x = a & b;\n"
              "    x = a | b;\n"
              "    x = a ^ b;\n"
              "    x = a < b;\n"
              "    x = a > b;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, PostfixIncrementDecrement) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x++;\n"
              "    x--;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, ChainedUnaryOperators) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = ~~a;\n"
              "    x = !!a;\n"
              "    x = -~a;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, OperatorInContinuousAssign) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c;\n"
              "  assign a = b & c;\n"
              "  assign c = ~b;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, BinaryOperatorMissingRightOperandFails) {
  auto r = Parse(
      "module m;\n"
      "  initial x = a +;\n"
      "endmodule\n");
  // §11.2 owns the report: the parser demands an expression where the right
  // operand belongs, and §5.5 states no rejection of its own.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
}

// A binary operator sits between two operands; with the left operand absent
// (here a purely-binary '*' opening the expression) the parse must fail. This
// is the mirror of the missing-right-operand case above.
TEST(LexicalConventionParsing, BinaryOperatorMissingLeftOperandFails) {
  auto r = Parse(
      "module m;\n"
      "  initial x = * b;\n"
      "endmodule\n");
  // §11.2 owns the report; §5.5 states no rejection of its own.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
}

TEST(LexicalConventionParsing, UnaryOperatorMissingOperandFails) {
  auto r = Parse(
      "module m;\n"
      "  initial x = ~;\n"
      "endmodule\n");
  // §11.2 owns the report; §5.5 states no rejection of its own.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
}

TEST(LexicalConventionParsing, ConditionalMissingColonFails) {
  auto r = Parse(
      "module m;\n"
      "  initial x = a ? b;\n"
      "endmodule\n");
  // §11.4.11 owns the conditional operator's ':' and reports its absence.
  EXPECT_TRUE(ReportedError(r.diags, "expected ':', got ';'", 2, "11.4.11"));
}

TEST(LexicalConventionParsing, ConditionalMissingFalseOperandFails) {
  auto r = Parse(
      "module m;\n"
      "  initial x = a ? b :;\n"
      "endmodule\n");
  // §11.2 owns the report; §5.5 states no rejection of its own.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
}

TEST(LexicalConventionParsing, ConditionalMissingTrueOperandFails) {
  auto r = Parse(
      "module m;\n"
      "  initial x = a ? : c;\n"
      "endmodule\n");
  // §11.2 owns the report; §5.5 states no rejection of its own.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
}

// The conditional operator separates three operands; with the first operand
// (the condition, before '?') absent, the parse must fail.
TEST(LexicalConventionParsing, ConditionalMissingConditionOperandFails) {
  auto r = Parse(
      "module m;\n"
      "  initial x = ? b : c;\n"
      "endmodule\n");
  // §11.2 owns the report; §5.5 states no rejection of its own.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
}

// The places an expression can be written, each holding `expr` on its second
// line: a procedural and a continuous assignment, a module's and a package's
// parameter, a function's return and a class property's initializer.
std::vector<std::string> ExpressionPlaces(const std::string& expr) {
  return {"module m;\n  initial x = " + expr + ";\nendmodule\n",
          "module m;\n  assign x = " + expr + ";\nendmodule\n",
          "module m;\n  localparam int P = " + expr + ";\nendmodule\n",
          "package p;\n  localparam int P = " + expr + ";\nendpackage\n",
          "module m;\n  function int f(int a, int b); return " + expr +
              "; endfunction\nendmodule\n",
          "class c;\n  int v = " + expr + ";\nendclass\n"};
}

// How many errors `diags` holds.
size_t ErrorsIn(const std::vector<Diagnostic>& diags) {
  return static_cast<size_t>(
      std::ranges::count(diags, DiagSeverity::kError, &Diagnostic::severity));
}

// The operators A.8.6 makes unary only: none of them is a binary operator too.
constexpr std::array<const char*, 4> kUnaryOnlyOperators = {"!", "~", "~&",
                                                            "~|"};

// §5.5: a unary operator stands to the left of its operand. One that has no
// binary form, written after its operand or between two operands, is
// reported under §5.5 at its line, once, wherever the expression stands; the
// operand after it is read with it rather than reported again.
TEST(LexicalConventionParsing, UnaryOnlyOperatorAfterAnOperandIsReported) {
  for (const char* op : kUnaryOnlyOperators) {
    const std::string kMessage =
        std::string("unary operator '") + op + "' cannot follow an operand";
    for (const std::string& expr :
         {std::string("a ") + op, std::string("a ") + op + " b"}) {
      for (const std::string& src : ExpressionPlaces(expr)) {
        auto r = Parse(src);
        EXPECT_TRUE(ReportedError(r.diags, kMessage, 2, "5.5")) << src;
        EXPECT_EQ(ErrorsIn(r.diags), 1u) << src;
      }
    }
  }
}

// The same operators to the left of their operand, and beside an operand of a
// binary operator, are accepted in every one of those places, as is `~^`,
// which is a binary operator as well as a unary one.
TEST(LexicalConventionParsing, UnaryOnlyOperatorBeforeItsOperandIsAccepted) {
  for (const char* op : kUnaryOnlyOperators) {
    for (const std::string& expr :
         {std::string(op) + " a", std::string("a & ") + op + "b"}) {
      for (const std::string& src : ExpressionPlaces(expr)) {
        EXPECT_TRUE(ParseOk(src)) << src;
      }
    }
  }
  for (const std::string& src : ExpressionPlaces("a ~^ b")) {
    EXPECT_TRUE(ParseOk(src)) << src;
  }
}

// The report stands alone however the expression around the misplaced operator
// is closed: by a comma between arguments, the colon of a conditional
// operator, or a closing parenthesis, bracket or brace.
TEST(LexicalConventionParsing,
     UnaryOnlyOperatorBeforeAClosingTokenIsOneReport) {
  for (const char* expr : {"f(a !, b)", "c ? a ! : b", "(a ~)", "y[a ~&]",
                           "{a ~|, b}", "{a ~|}"}) {
    const std::string kSrc =
        std::string("module m;\n  initial x = ") + expr + ";\nendmodule\n";
    auto r = Parse(kSrc);
    EXPECT_TRUE(ReportedError(r.diags, "cannot follow an operand", 2, "5.5"))
        << expr;
    EXPECT_EQ(ErrorsIn(r.diags), 1u) << expr;
  }
}

}  // namespace
