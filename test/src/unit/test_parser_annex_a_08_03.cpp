#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ExpressionParsing, ExprOperatorAssignment) {
  auto r = Parse("module m; initial x = (y += 1); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, IncExpression) {
  auto r = Parse("module m; initial begin i++; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, DecExpression) {
  auto r = Parse("module m; initial begin --j; end endmodule\n");
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

TEST(ExpressionParsing, TaggedUnionExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial x = tagged Valid 42;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTagged);
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

// §A.8.3: inc_or_dec_expression — prefix ++ form
TEST(ExpressionParsing, PrefixIncExpression) {
  auto r = Parse("module m; initial begin ++i; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.8.3: inc_or_dec_expression — postfix -- form
TEST(ExpressionParsing, PostfixDecExpression) {
  auto r = Parse("module m; initial begin j--; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.8.3: constant_expression in parameter declaration
TEST(ExpressionParsing, ConstantExpressionInParameter) {
  auto r = Parse("module m; parameter P = 2 + 3; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.8.3: constant_expression with unary operator in localparam
TEST(ExpressionParsing, ConstantExpressionUnaryInLocalparam) {
  auto r = Parse("module m; localparam P = ~8'hFF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.8.3: constant_expression with ternary in parameter
TEST(ExpressionParsing, ConstantExpressionTernaryInParameter) {
  auto r = Parse(
      "module m;\n"
      "  parameter A = 1;\n"
      "  parameter B = (A > 0) ? 8 : 16;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.8.3: constant_mintypmax_expression in specparam
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

// §A.8.3: constant_param_expression — $ in queue dimension
TEST(ExpressionParsing, ConstantParamExpressionDollar) {
  auto r = Parse("module m; int q[$]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.8.3: constant_param_expression — $ with bound in queue dimension
TEST(ExpressionParsing, ConstantParamExpressionDollarWithBound) {
  auto r = Parse("module m; int q[$:255]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.8.3: param_expression — ordered parameter override
TEST(ExpressionParsing, ParamExpressionInOverride) {
  auto r = Parse(
      "module m;\n"
      "  sub #(8) inst(.a(x));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.8.3: param_expression — named parameter override
TEST(ExpressionParsing, ParamExpressionNamedOverride) {
  auto r = Parse(
      "module m;\n"
      "  sub #(.WIDTH(16)) inst(.a(x));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.8.3: param_expression — data_type as parameter override
TEST(ExpressionParsing, ParamExpressionDataTypeOverride) {
  auto r = Parse(
      "module m;\n"
      "  sub #(.T(logic [7:0])) inst(.a(x));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.8.3: constant_range in packed dimension
TEST(ExpressionParsing, ConstantRangeInPackedDimension) {
  auto r = Parse("module m; logic [7:0] x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.8.3: constant_range with expressions
TEST(ExpressionParsing, ConstantRangeWithExpressions) {
  auto r = Parse(
      "module m;\n"
      "  parameter N = 8;\n"
      "  logic [N-1:0] x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.8.3: genvar_expression in generate for loop
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

// §A.8.3: genvar_expression with inline genvar declaration
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

// §A.8.3: module_path_conditional_expression — state-dependent path
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

// §A.8.3: module_path_expression — unary operator in specify condition
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

// §A.8.3: module_path_expression — binary operator in specify condition
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

// §A.8.3: module_path_mintypmax_expression — multiple delay values
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

// §A.8.3: inside_expression with open_value_range
TEST(ExpressionParsing, InsideExpressionWithRanges) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x inside {[0:5], [10:20], 42}) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.8.3: tagged_union_expression without inner expression
TEST(ExpressionParsing, TaggedUnionExpressionVoid) {
  auto r = Parse(
      "module m;\n"
      "  initial x = tagged Invalid;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTagged);
}

// §A.8.3: expression — all binary operators parse
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

// §A.8.3: expression — all unary operators parse
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

// §A.8.3: Error — missing colon in ternary
TEST(ExpressionParsing, ErrorMissingTernaryColon) {
  auto r = Parse("module m; initial x = a ? b c; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §A.8.3: Error — missing brace in inside expression
TEST(ExpressionParsing, ErrorInsideMissingBrace) {
  EXPECT_FALSE(ParseOk("module m; initial if (x inside 1) a = 1; endmodule\n"));
}

// §A.8.3: Error — incomplete part select range
TEST(ExpressionParsing, ErrorIncompletePartSelect) {
  EXPECT_FALSE(ParseOk("module m; initial x = a[7:]; endmodule\n"));
}

}  // namespace
