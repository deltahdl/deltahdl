#include <gtest/gtest.h>

#include <cstddef>
#include <initializer_list>
#include <set>
#include <string_view>
#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

void ExpectSubtreeLocated(const Expr* e, std::set<ExprKind>& reached) {
  if (e == nullptr) return;
  EXPECT_TRUE(e->range.start.IsValid())
      << "an expression node of ExprKind value " << static_cast<int>(e->kind)
      << " carries no position";
  reached.insert(e->kind);
  for (const Expr* sub : {e->lhs, e->rhs, e->condition, e->true_expr,
                          e->false_expr, e->base, e->index, e->index_end,
                          e->repeat_count, e->with_expr, e->stream_range}) {
    ExpectSubtreeLocated(sub, reached);
  }
  for (const Expr* sub : e->elements) ExpectSubtreeLocated(sub, reached);
  for (const Expr* sub : e->args) ExpectSubtreeLocated(sub, reached);
}

void ExpectStmtExprsLocated(const Stmt* s, std::set<ExprKind>& reached) {
  ASSERT_NE(s, nullptr);
  for (const Expr* root : {s->lhs, s->rhs, s->expr, s->condition, s->delay}) {
    ExpectSubtreeLocated(root, reached);
  }
}

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
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ':', got identifier", 1, "11.4.11"));
}

TEST(ExpressionParsing, ErrorInsideMissingBrace) {
  auto r = Parse("module m; initial if (x inside 1) a = 1; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected '{', got integer literal", 1,
                            "11.4.13"));
}

TEST(ExpressionParsing, ErrorIncompletePartSelect) {
  auto r = Parse("module m; initial x = a[7:]; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
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
  auto r = Parse(
      "module m;\n"
      "  initial x = tagged ;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 2, "7.3.2"));
}

TEST(ExpressionParsing, ErrorBinaryOperatorMissingRhs) {
  auto r = Parse(
      "module m;\n"
      "  initial x = a + ;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
}

TEST(ExpressionParsing, UnaryOperatorWithAttribute) {
  auto r = Parse("module m; initial x = ~ (* keep *) a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
}

TEST(ExpressionParsing, ConstantUnaryOperatorWithAttribute) {
  auto r = Parse("module m; localparam Q = - (* keep *) 8'd1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, PrefixIncrementWithAttribute) {
  auto r = Parse("module m; initial begin ++ (* keep *) i; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, PostfixDecrementWithAttribute) {
  auto r = Parse("module m; initial begin j (* keep *) --; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

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

TEST(ExpressionParsing, ErrorPrefixIncrementMissingOperand) {
  auto r = Parse("module m; initial begin ++; end endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

TEST(ExpressionParsing, ErrorIndexedPartSelectMissingWidth) {
  auto r = Parse("module m; initial x = a[0+:]; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

TEST(ExpressionParsing, ErrorConstantRangeMissingBound) {
  auto r = Parse("module m; logic [7:] x; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

TEST(ExpressionParsing, ConstantRangeReversedBounds) {
  auto r = Parse(
      "module m;\n"
      "  logic [0:7] x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, EveryParsedExpressionCarriesAPosition) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = 1;\n"
      "    x = 1.5;\n"
      "    x = \"s\";\n"
      "    x = '1;\n"
      "    x = a;\n"
      "    x = $clog2(8);\n"
      "    x = ~a;\n"
      "    x = a + b;\n"
      "    x = sel ? a : b;\n"
      "    x = {a, b};\n"
      "    x = {4{a}};\n"
      "    x = v[7:4];\n"
      "    x = s.f;\n"
      "    x = fn(1);\n"
      "    x = '{1, 2};\n"
      "    x = int'(a);\n"
      "    x = type(a);\n"
      "    x = a inside {1, 2};\n"
      "    x = {>> byte {v}};\n"
      "    x = tagged Valid 42;\n"
      "    x = {>> {q with [1:2]}};\n"
      "    j--;\n"
      "    if (a &&& b) x = 1;\n"
      "    if (a matches 3) x = 1;\n"
      "    foreach (obj.arr[i]) x = i;\n"
      "    #10ns x = 2;\n"
      "    #(1:2:3) x = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  std::set<ExprKind> reached;
  std::vector<Stmt*> stmts = AllInitialStmts(r);
  ASSERT_FALSE(stmts.empty());
  for (const Stmt* s : stmts) ExpectStmtExprsLocated(s, reached);

  const ExprKind kEveryKind[] = {ExprKind::kIntegerLiteral,
                                 ExprKind::kRealLiteral,
                                 ExprKind::kTimeLiteral,
                                 ExprKind::kStringLiteral,
                                 ExprKind::kUnbasedUnsizedLiteral,
                                 ExprKind::kIdentifier,
                                 ExprKind::kSystemCall,
                                 ExprKind::kUnary,
                                 ExprKind::kBinary,
                                 ExprKind::kTernary,
                                 ExprKind::kConcatenation,
                                 ExprKind::kReplicate,
                                 ExprKind::kSelect,
                                 ExprKind::kMemberAccess,
                                 ExprKind::kCall,
                                 ExprKind::kAssignmentPattern,
                                 ExprKind::kCast,
                                 ExprKind::kTypeRef,
                                 ExprKind::kPostfixUnary,
                                 ExprKind::kInside,
                                 ExprKind::kStreamingConcat,
                                 ExprKind::kMinTypMax,
                                 ExprKind::kTagged};
  for (ExprKind kind : kEveryKind) {
    EXPECT_EQ(reached.count(kind), 1u)
        << "no construct in the source reached ExprKind value "
        << static_cast<int>(kind);
  }
}

TEST(ExpressionParsing, ErrorIncrementOperandIsNoVariableLvalue) {
  auto r = Parse(
      "module m;\n"
      "  int a, b;\n"
      "  function int f(int x); return x; endfunction\n"
      "  initial begin\n"
      "    ++3;\n"
      "    ++(a + b);\n"
      "    --(a);\n"
      "    f(1)++;\n"
      "    ++a[0];\n"
      "  end\n"
      "endmodule\n");
  constexpr std::string_view kMessage =
      "an increment or decrement's operand is a variable_lvalue; this one is "
      "not";
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 5, "A.8.3"));
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 6, "A.8.3"));
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 7, "A.8.3"));
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 8, "A.8.3"));
  EXPECT_FALSE(ReportedError(r.diags, kMessage, 9, "A.8.3"));
}

TEST(ExpressionParsing, ErrorParenthesizedAssignmentTargetIsNoVariableLvalue) {
  auto r = Parse(
      "module m;\n"
      "  int x, y, a, b;\n"
      "  initial begin\n"
      "    x = (3 = y);\n"
      "    x = ((a + b) += 1);\n"
      "    x = ((a) = y);\n"
      "    x = (a = y);\n"
      "  end\n"
      "endmodule\n");
  constexpr std::string_view kMessage =
      "an assignment within an expression assigns a variable_lvalue; this "
      "target is none";
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 4, "A.6.2"));
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 5, "A.6.2"));
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 6, "A.6.2"));
  EXPECT_FALSE(ReportedError(r.diags, kMessage, 7, "A.6.2"));
}

TEST(ExpressionParsing, TaggedMemberValueIsAPrimary) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = tagged Valid 3 + 4;\n"
      "    x = tagged Invalid - 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (size_t n : {0u, 1u}) {
    Stmt* s = NthInitialStmt(r, n);
    ASSERT_NE(s, nullptr);
    ASSERT_NE(s->rhs, nullptr);
    ASSERT_EQ(s->rhs->kind, ExprKind::kBinary) << n;
    ASSERT_NE(s->rhs->lhs, nullptr);
    EXPECT_EQ(s->rhs->lhs->kind, ExprKind::kTagged) << n;
  }
  EXPECT_EQ(NthInitialStmt(r, 0)->rhs->op, TokenKind::kPlus);
  EXPECT_NE(NthInitialStmt(r, 0)->rhs->lhs->lhs, nullptr);
  EXPECT_EQ(NthInitialStmt(r, 1)->rhs->op, TokenKind::kMinus);
  EXPECT_EQ(NthInitialStmt(r, 1)->rhs->lhs->lhs, nullptr);
}

TEST(ExpressionParsing, TaggedPatternMemberTakesAConstantExpression) {
  auto r = Parse(
      "module m; initial if (x matches tagged M 1 + 2) y = 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  Stmt* s = FirstInitialStmt(r);
  ASSERT_NE(s, nullptr);
  ASSERT_NE(s->condition, nullptr);
  const Expr* tagged = s->condition->rhs;
  ASSERT_NE(tagged, nullptr);
  ASSERT_EQ(tagged->kind, ExprKind::kTagged);
  ASSERT_NE(tagged->lhs, nullptr);
  EXPECT_EQ(tagged->lhs->kind, ExprKind::kBinary);
}

TEST(ExpressionParsing, ClassParameterValueTakesAMinTypMax) {
  auto r = Parse(
      "class C #(int P = 0);\n"
      "  static int v = P;\n"
      "endclass\n"
      "module m;\n"
      "  C #(1:2:3) h;\n"
      "  C #(.P(1:2:3)) g;\n"
      "  C #(.P()) e;\n"
      "  int x, y, z;\n"
      "  initial x = C#(4:5:6)::v;\n"
      "  initial y = C#(.P(4:5:6))::v;\n"
      "  initial z = C#(.P())::v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, ClassTypeParameterValueTakesAnAggregate) {
  auto r = Parse(
      "class C #(type T = int);\n"
      "  T v;\n"
      "endclass\n"
      "module m;\n"
      "  C #(struct packed { bit a; byte b; }) h;\n"
      "  C #(enum bit { A, B }) g;\n"
      "  C #(.T(union packed { bit a; bit b; })) k;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
