#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ExpressionParsing, ExprOperatorAssignment) {
  auto r = Parse("module m; initial x = (y += 1); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ConditionalExpression) {
  auto r = Parse("module m; initial x = a ? b : c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
}

TEST(ExpressionParsing, InsideExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x inside {1, 2, [5:10]}) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, TaggedUnionWithValue) {
  auto r = Parse("module m; initial x = tagged Valid 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTagged);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->text, "Valid");
  ASSERT_NE(rhs->lhs, nullptr);
}

TEST(ExpressionParsing, TaggedUnionWithAssignmentPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = tagged Add '{ 1, 2, 3 };\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTagged);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->text, "Add");
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kAssignmentPattern);
}

TEST(ExpressionParsing, NestedTaggedUnionExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = tagged Jmp (tagged JmpU 239);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTagged);
  EXPECT_EQ(rhs->rhs->text, "Jmp");
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kTagged);
  EXPECT_EQ(rhs->lhs->rhs->text, "JmpU");
}

TEST(ExpressionParsing, TaggedUnionParenthesizedExpr) {
  auto r = Parse("module m; initial x = tagged Valid (23+34); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTagged);
  EXPECT_EQ(rhs->rhs->text, "Valid");
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kBinary);
}

TEST(ExpressionParsing, MintypMaxExpression) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1:2:3);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, PartSelectRange) {
  auto r = Parse("module m; initial x = a[7:4]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
}

TEST(ExpressionParsing, IndexedRangePlus) {
  auto r = Parse("module m; initial x = a[0+:4]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
}

TEST(ExpressionParsing, IndexedRangeMinus) {
  auto r = Parse("module m; initial x = a[7-:4]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_minus);
}

TEST(ExpressionParsing, UnaryOperatorExpr) {
  auto r = Parse("module m; initial x = ~a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
}

TEST(ExpressionParsing, BinaryOperatorExpr) {
  auto r = Parse("module m; initial x = a + b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
}

TEST(ExpressionParsing, NestedTernary) {
  auto r = Parse("module m; initial x = a ? b ? c : d : e; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
}

TEST(ExpressionParsing, PrefixIncExpression) {
  auto r = Parse("module m; initial begin ++i; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, PostfixDecExpression) {
  auto r = Parse("module m; initial begin j--; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ConstantExpressionInParameter) {
  auto r = Parse("module m; parameter P = 2 + 3; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ConstantExpressionUnaryInLocalparam) {
  auto r = Parse("module m; localparam P = ~8'hFF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ConstantExpressionTernaryInParameter) {
  auto r = Parse(
      "module m;\n"
      "  parameter A = 1;\n"
      "  parameter B = (A > 0) ? 8 : 16;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ConstantMintypMaxInSpecparam) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tRise = 1:2:3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ConstantParamExpressionDollar) {
  auto r = Parse("module m; int q[$]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ConstantParamExpressionDollarWithBound) {
  auto r = Parse("module m; int q[$:255]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.8.3 constant_param_expression ::= constant_mintypmax_expression |
// data_type | $. The '$' alternative as a value-parameter default, built from
// real parameter-declaration syntax (distinct from a queue dimension's '$').
TEST(ExpressionParsing, ConstantParamExpressionDollarDefault) {
  auto r = Parse("module m; parameter P = $; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ParamExpressionInOverride) {
  auto r = Parse(
      "module m;\n"
      "  sub #(8) inst(.a(x));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ParamExpressionNamedOverride) {
  auto r = Parse(
      "module m;\n"
      "  sub #(.WIDTH(16)) inst(.a(x));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ParamExpressionDataTypeOverride) {
  auto r = Parse(
      "module m;\n"
      "  sub #(.T(logic [7:0])) inst(.a(x));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ParamExpressionDollarOverride) {
  auto r = Parse(
      "module m;\n"
      "  sub #(.MAX_SIZE($)) inst(.a(x));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ConstantRangeInPackedDimension) {
  auto r = Parse("module m; logic [7:0] x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ConstantRangeWithExpressions) {
  auto r = Parse(
      "module m;\n"
      "  parameter N = 8;\n"
      "  logic [N-1:0] x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, GenvarExpression) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : gen\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, GenvarExpressionInlineDecl) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i = i + 1) begin : gen\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ModulePathConditionalExpression) {
  auto r = Parse(
      "module m(input a, b, output c);\n"
      "  specify\n"
      "    if (a) (a => c) = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ModulePathExpressionUnary) {
  auto r = Parse(
      "module m(input a, output c);\n"
      "  specify\n"
      "    if (~a) (a => c) = 2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ModulePathExpressionBinary) {
  auto r = Parse(
      "module m(input a, b, output c);\n"
      "  specify\n"
      "    if (a & b) (a => c) = 3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ModulePathMintypMaxMultipleDelays) {
  auto r = Parse(
      "module m(input a, output c);\n"
      "  specify\n"
      "    (a => c) = (1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, TaggedUnionWithoutValue) {
  auto r = Parse("module m; initial x = tagged Invalid; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTagged);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->text, "Invalid");
  EXPECT_EQ(rhs->lhs, nullptr);
}

TEST(ExpressionParsing, AllBinaryOperators) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = a + b;\n"
      "    x = a - b;\n"
      "    x = a * b;\n"
      "    x = a / b;\n"
      "    x = a % b;\n"
      "    x = a ** b;\n"
      "    x = a & b;\n"
      "    x = a | b;\n"
      "    x = a ^ b;\n"
      "    x = a ~^ b;\n"
      "    x = a << b;\n"
      "    x = a >> b;\n"
      "    x = a <<< b;\n"
      "    x = a >>> b;\n"
      "    x = a == b;\n"
      "    x = a != b;\n"
      "    x = a === b;\n"
      "    x = a !== b;\n"
      "    x = a && b;\n"
      "    x = a || b;\n"
      "    x = a < b;\n"
      "    x = a > b;\n"
      "    x = a <= b;\n"
      "    x = a >= b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, AllUnaryOperators) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = +a;\n"
      "    x = -a;\n"
      "    x = !a;\n"
      "    x = ~a;\n"
      "    x = &a;\n"
      "    x = ~&a;\n"
      "    x = |a;\n"
      "    x = ~|a;\n"
      "    x = ^a;\n"
      "    x = ~^a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ErrorMissingTernaryColon) {
  auto r = Parse("module m; initial x = a ? b c; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ExpressionParsing, ErrorInsideMissingBrace) {
  EXPECT_FALSE(ParseOk("module m; initial if (x inside 1) a = 1; endmodule\n"));
}

TEST(ExpressionParsing, ErrorIncompletePartSelect) {
  EXPECT_FALSE(ParseOk("module m; initial x = a[7:]; endmodule\n"));
}

TEST(ExpressionParsing, ConstantIndexedRangePlusInPackedDimSelect) {
  auto r = Parse(
      "module m;\n"
      "  parameter BASE = 8;\n"
      "  parameter WIDTH = 4;\n"
      "  logic [15:0] data;\n"
      "  logic [WIDTH-1:0] hi;\n"
      "  initial hi = data[BASE+:WIDTH];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ConstantIndexedRangeMinusInPackedDimSelect) {
  auto r = Parse(
      "module m;\n"
      "  parameter TOP = 15;\n"
      "  parameter WIDTH = 4;\n"
      "  logic [15:0] data;\n"
      "  logic [WIDTH-1:0] hi;\n"
      "  initial hi = data[TOP-:WIDTH];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ErrorTaggedExpressionMissingMember) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  initial x = tagged ;\n"
              "endmodule\n"));
}

TEST(ExpressionParsing, ErrorBinaryOperatorMissingRhs) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  initial x = a + ;\n"
              "endmodule\n"));
}

// §A.8.3 expression ::= unary_operator { attribute_instance } primary — the
// optional attribute sits between the unary operator and its operand.
TEST(ExpressionParsing, UnaryOperatorWithAttribute) {
  auto r = Parse("module m; initial x = ~ (* keep *) a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
}

// §A.8.3 constant_expression ::= unary_operator { attribute_instance }
// constant_primary — the attributed unary form in a constant context.
TEST(ExpressionParsing, ConstantUnaryOperatorWithAttribute) {
  auto r = Parse("module m; localparam Q = - (* keep *) 8'd1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.8.3 inc_or_dec_expression ::= inc_or_dec_operator { attribute_instance }
// variable_lvalue — prefix form with an intervening attribute.
TEST(ExpressionParsing, PrefixIncrementWithAttribute) {
  auto r = Parse("module m; initial begin ++ (* keep *) i; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.8.3 inc_or_dec_expression ::= variable_lvalue { attribute_instance }
// inc_or_dec_operator — postfix form with an intervening attribute.
TEST(ExpressionParsing, PostfixDecrementWithAttribute) {
  auto r = Parse("module m; initial begin j (* keep *) --; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.8.3 module_path_conditional_expression ::= module_path_expression ?
// { attribute_instance } module_path_expression : module_path_expression —
// the ternary form as a state-dependent path condition.
TEST(ExpressionParsing, ModulePathConditionalTernaryCondition) {
  auto r = Parse(
      "module m(input a, b, sel, output c);\n"
      "  specify\n"
      "    if (sel ? a : b) (a => c) = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.8.3 inc_or_dec_expression requires a variable_lvalue operand; a prefix
// ++/-- with no operand must be rejected.
TEST(ExpressionParsing, ErrorPrefixIncrementMissingOperand) {
  EXPECT_FALSE(ParseOk("module m; initial begin ++; end endmodule\n"));
}

// §A.8.3 indexed_range ::= expression +: constant_expression — the width after
// '+:' is mandatory; omitting it must be rejected.
TEST(ExpressionParsing, ErrorIndexedPartSelectMissingWidth) {
  EXPECT_FALSE(ParseOk("module m; initial x = a[0+:]; endmodule\n"));
}

// §A.8.3 constant_range ::= constant_expression : constant_expression — both
// bounds are mandatory; a packed dimension missing its right bound must be
// rejected.
TEST(ExpressionParsing, ErrorConstantRangeMissingBound) {
  EXPECT_FALSE(ParseOk("module m; logic [7:] x; endmodule\n"));
}

TEST(ExpressionParsing, ConstantRangeReversedBounds) {
  auto r = Parse(
      "module m;\n"
      "  logic [0:7] x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
