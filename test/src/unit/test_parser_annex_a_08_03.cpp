#include <set>
#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// Every expression node the tree under `e` holds, asserting each carries a
// position and recording which ExprKind values were reached. A node built with
// no position makes any report standing at it print "<unknown location>"
// instead of a file, line and column, because SourceManager::FormatLoc in
// src/common/source_mgr.cpp writes that sentence for a SourceLoc that fails
// SourceLoc::IsValid(), and DiagEngine::Emit in src/common/diagnostic.cpp then
// drops the source line and the caret as well.
void ExpectSubtreeLocated(const Expr* e, std::set<ExprKind>& reached) {
  if (e == nullptr) return;
  EXPECT_TRUE(e->range.start.IsValid())
      << "an expression node of ExprKind value " << static_cast<int>(e->kind)
      << " carries no position";
  reached.insert(e->kind);
  for (const Expr* sub :
       {e->lhs, e->rhs, e->condition, e->true_expr, e->false_expr, e->base,
        e->index, e->index_end, e->repeat_count, e->with_expr}) {
    ExpectSubtreeLocated(sub, reached);
  }
  for (const Expr* sub : e->elements) ExpectSubtreeLocated(sub, reached);
  for (const Expr* sub : e->args) ExpectSubtreeLocated(sub, reached);
}

// The expressions a procedural statement roots: an assignment's two sides, an
// expression statement's expression, a conditional statement's predicate, and
// a delay control's delay value.
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
  // §11.4.11 owns the conditional operator's ':'.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ':', got identifier", 1, "11.4.11"));
}

TEST(ExpressionParsing, ErrorInsideMissingBrace) {
  auto r = Parse("module m; initial if (x inside 1) a = 1; endmodule\n");
  // §11.4.13 owns the open_range_list braces the 'inside' operator requires.
  EXPECT_TRUE(ReportedError(r.diags, "expected '{', got integer literal", 1,
                            "11.4.13"));
}

TEST(ExpressionParsing, ErrorIncompletePartSelect) {
  auto r = Parse("module m; initial x = a[7:]; endmodule\n");
  // §11.2 owns the report Parser::ParsePrimaryExpr makes for the missing
  // right bound; §11.5.1 states the part-select itself.
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
  // §7.3.2 owns the member name a tagged union expression names.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 2, "7.3.2"));
}

TEST(ExpressionParsing, ErrorBinaryOperatorMissingRhs) {
  auto r = Parse(
      "module m;\n"
      "  initial x = a + ;\n"
      "endmodule\n");
  // §11.2 owns the report Parser::ParsePrimaryExpr makes for the missing
  // right operand.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
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
  auto r = Parse("module m; initial begin ++; end endmodule\n");
  // §11.2 owns the report Parser::ParsePrimaryExpr makes for the missing
  // operand of the prefix '++'.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

// §A.8.3 indexed_range ::= expression +: constant_expression — the width after
// '+:' is mandatory; omitting it must be rejected.
TEST(ExpressionParsing, ErrorIndexedPartSelectMissingWidth) {
  auto r = Parse("module m; initial x = a[0+:]; endmodule\n");
  // §11.2 owns the report Parser::ParsePrimaryExpr makes for the missing
  // width; §11.5.1 states the indexed part-select itself.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

// §A.8.3 constant_range ::= constant_expression : constant_expression — both
// bounds are mandatory; a packed dimension missing its right bound must be
// rejected.
TEST(ExpressionParsing, ErrorConstantRangeMissingBound) {
  auto r = Parse("module m; logic [7:] x; endmodule\n");
  // §11.2 owns the report Parser::ParsePrimaryExpr makes for the missing
  // right bound; §6.9 states the packed dimension it belongs to.
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

// Covers every construction site in src/parser/ that builds an §A.8.3
// expression, by holding one construct for each of the twenty-three values of
// ExprKind and asserting that every node the parse produced carries a position.
// Twelve sites assigned none before this commit, so a report standing at one of
// their nodes named the rule it enforced and not where the source broke it.
// Parser::TryParseSpecialInfix is the reason the whole of ExprKind::kTernary
// was affected: §11.4.11 has one construction site in the parser and it was one
// of the twelve, so a conditional expression rendered as "<unknown location>".
// Parser::ParseWithClauseRange (§7.12.1), Parser::ParseInsideValueRange
// (§11.4.13), ParserPortHelpers::ParseNonAnsiPortSelect (§23.2.2.1),
// Parser::ParseAssocIndexDim (§7.8), Parser::ParseUnpackedDims (§7.4.2, §7.8.1
// and §7.10) and Parser::ParseForeachArrayId (§12.7.3) are the rest.
//
// A construction site added later cannot pass this case without setting
// range.start, which is what the per-construct cases beside it cannot say.
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
      "    q.reverse with [1:2];\n"
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

  // Which constructs the source actually reached, so a construct that stops
  // parsing shrinks the coverage loudly rather than silently.
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

}  // namespace
