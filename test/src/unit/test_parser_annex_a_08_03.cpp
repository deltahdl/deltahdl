// Tests for A.8.3 — Expressions — Parser

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

static Stmt *FirstInitialStmt(ParseResult &r) {
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

static Expr *FirstInitialExpr(ParseResult &r) {
  auto *stmt = FirstInitialStmt(r);
  return stmt ? stmt->expr : nullptr;
}

static Expr *FirstInitialRHS(ParseResult &r) {
  auto *stmt = FirstInitialStmt(r);
  return stmt ? stmt->rhs : nullptr;
}

static Expr *FirstContAssignRHS(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign)
      return item->assign_rhs;
  }
  return nullptr;
}

} // namespace

// =============================================================================
// A.8.3 Expressions — inc_or_dec_expression
// =============================================================================

// § inc_or_dec_expression ::= inc_or_dec_operator { attribute_instance }
// variable_lvalue

TEST(ParserA83, PrefixIncrement) {
  auto r = Parse("module m; initial ++x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kUnary);
  EXPECT_EQ(expr->op, TokenKind::kPlusPlus);
}

TEST(ParserA83, PrefixDecrement) {
  auto r = Parse("module m; initial --x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kUnary);
  EXPECT_EQ(expr->op, TokenKind::kMinusMinus);
}

// § inc_or_dec_expression ::= variable_lvalue { attribute_instance }
// inc_or_dec_operator

TEST(ParserA83, PostfixIncrement) {
  auto r = Parse("module m; initial x++; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(expr->op, TokenKind::kPlusPlus);
}

TEST(ParserA83, PostfixDecrement) {
  auto r = Parse("module m; initial x--; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(expr->op, TokenKind::kMinusMinus);
}

TEST(ParserA83, PrefixIncrementOnSelect) {
  auto r = Parse("module m; initial ++arr[0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kUnary);
  EXPECT_EQ(expr->lhs->kind, ExprKind::kSelect);
}

TEST(ParserA83, PostfixDecrementOnMember) {
  auto r = Parse("module m; initial s.field--; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(expr->op, TokenKind::kMinusMinus);
}

// =============================================================================
// A.8.3 Expressions — conditional_expression
// =============================================================================

// § conditional_expression ::= cond_predicate ? { attribute_instance }
// expression : expression

TEST(ParserA83, ConditionalExprSimple) {
  auto r = Parse("module m; initial x = a ? b : c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  ASSERT_NE(rhs->true_expr, nullptr);
  ASSERT_NE(rhs->false_expr, nullptr);
}

TEST(ParserA83, ConditionalExprNested) {
  auto r = Parse("module m; initial x = a ? b ? c : d : e; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kTernary);
}

TEST(ParserA83, ConditionalExprWithBinaryCondition) {
  auto r = Parse("module m; initial x = (a > b) ? a : b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
}

// =============================================================================
// A.8.3 Expressions — constant_expression
// =============================================================================

// § constant_expression ::= constant_primary

TEST(ParserA83, ConstantExprPrimary) {
  auto r = Parse("module m #(parameter int P = 42);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &params = r.cu->modules[0]->params;
  ASSERT_GE(params.size(), 1u);
  EXPECT_EQ(params[0].second->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(params[0].second->int_val, 42u);
}

// § constant_expression ::= unary_operator { attribute_instance }
// constant_primary

TEST(ParserA83, ConstantExprUnary) {
  auto r = Parse("module m #(parameter int P = -1);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &params = r.cu->modules[0]->params;
  ASSERT_GE(params.size(), 1u);
  EXPECT_EQ(params[0].second->kind, ExprKind::kUnary);
  EXPECT_EQ(params[0].second->op, TokenKind::kMinus);
}

// § constant_expression ::= constant_expression binary_operator
// { attribute_instance } constant_expression

TEST(ParserA83, ConstantExprBinary) {
  auto r = Parse("module m #(parameter int P = 3 + 4);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &params = r.cu->modules[0]->params;
  ASSERT_GE(params.size(), 1u);
  EXPECT_EQ(params[0].second->kind, ExprKind::kBinary);
  EXPECT_EQ(params[0].second->op, TokenKind::kPlus);
}

// § constant_expression ::= constant_expression ? { attribute_instance }
// constant_expression : constant_expression

TEST(ParserA83, ConstantExprTernary) {
  auto r = Parse("module m #(parameter int P = 1 ? 10 : 20);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &params = r.cu->modules[0]->params;
  ASSERT_GE(params.size(), 1u);
  EXPECT_EQ(params[0].second->kind, ExprKind::kTernary);
}

// =============================================================================
// A.8.3 Expressions — constant_mintypmax_expression
// =============================================================================

// § constant_mintypmax_expression ::= constant_expression :
// constant_expression : constant_expression

TEST(ParserA83, ConstantMinTypMaxInSpecparam) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    specparam tpd = 1:2:3;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.3 Expressions — constant_param_expression / param_expression
// =============================================================================

// § constant_param_expression ::= constant_mintypmax_expression | data_type | $

TEST(ParserA83, ParamExprLiteralValue) {
  auto r = Parse("module m #(parameter int P = 10);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->params[0].second->kind,
            ExprKind::kIntegerLiteral);
}

TEST(ParserA83, ParamExprBinaryOp) {
  auto r = Parse("module m #(parameter int P = 2 * 8);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->params[0].second->kind, ExprKind::kBinary);
}

// =============================================================================
// A.8.3 Expressions — constant_range_expression / constant_range
// =============================================================================

// § constant_range ::= constant_expression : constant_expression

TEST(ParserA83, ConstantRangeInPackedDim) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] x;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
}

// § constant_range_expression in bit-select context

TEST(ParserA83, ConstantRangeExprBitSelect) {
  auto r = Parse("module m; initial x = data[3]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index_end, nullptr);
}

// § constant_range in part-select context

TEST(ParserA83, ConstantRangePartSelect) {
  auto r = Parse("module m; initial x = data[7:4]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
}

// =============================================================================
// A.8.3 Expressions — constant_indexed_range / indexed_range
// =============================================================================

// § constant_indexed_range ::= constant_expression +: constant_expression

TEST(ParserA83, IndexedRangePlusColon) {
  auto r = Parse("module m; initial x = data[2+:4]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
}

// § constant_indexed_range ::= constant_expression -: constant_expression

TEST(ParserA83, IndexedRangeMinusColon) {
  auto r = Parse("module m; initial x = data[7-:4]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_FALSE(rhs->is_part_select_plus);
  EXPECT_TRUE(rhs->is_part_select_minus);
}

// § indexed_range with variable base

TEST(ParserA83, IndexedRangeVariableBase) {
  auto r = Parse("module m; initial x = data[i+:8]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
  EXPECT_EQ(rhs->index->kind, ExprKind::kIdentifier);
}

// =============================================================================
// A.8.3 Expressions — expression
// =============================================================================

// § expression ::= primary

TEST(ParserA83, ExprPrimary) {
  auto r = Parse("module m; initial x = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// § expression ::= unary_operator { attribute_instance } primary

TEST(ParserA83, ExprUnaryOp) {
  auto r = Parse("module m; initial x = ~a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
}

TEST(ParserA83, ExprUnaryNot) {
  auto r = Parse("module m; initial x = !a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kBang);
}

// § expression ::= expression binary_operator { attribute_instance } expression

TEST(ParserA83, ExprBinaryAdd) {
  auto r = Parse("module m; initial x = a + b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}

TEST(ParserA83, ExprBinaryLogicalAnd) {
  auto r = Parse("module m; initial x = a && b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
}

TEST(ParserA83, ExprPrecedenceChain) {
  auto r = Parse("module m; initial x = a + b * c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
  // b * c should be the RHS of the + node
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kStar);
}

// § expression ::= ( operator_assignment )

TEST(ParserA83, ExprOperatorAssignment) {
  auto r = Parse("module m; initial x = (y += 1); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § expression ::= inc_or_dec_expression (as sub-expression)

TEST(ParserA83, IncDecAsExpression) {
  auto r = Parse("module m; initial x = ++y; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kPlusPlus);
}

// =============================================================================
// A.8.3 Expressions — tagged_union_expression
// =============================================================================

// § tagged_union_expression ::= tagged member_identifier [ primary ]

TEST(ParserA83, TaggedUnionWithValue) {
  auto r = Parse("module m; initial x = tagged Valid 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTagged);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->text, "Valid");
  ASSERT_NE(rhs->lhs, nullptr);
}

TEST(ParserA83, TaggedUnionWithoutValue) {
  auto r = Parse("module m; initial x = tagged Invalid; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTagged);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->text, "Invalid");
  EXPECT_EQ(rhs->lhs, nullptr);
}

// =============================================================================
// A.8.3 Expressions — inside_expression
// =============================================================================

// § inside_expression ::= expression inside { range_list }

TEST(ParserA83, InsideExprSingleValue) {
  auto r = Parse("module m; initial x = a inside {3}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kInside);
  EXPECT_EQ(rhs->elements.size(), 1u);
}

TEST(ParserA83, InsideExprMultipleValues) {
  auto r = Parse("module m; initial x = a inside {1, 2, 3}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kInside);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

TEST(ParserA83, InsideExprWithRange) {
  auto r = Parse("module m; initial x = a inside {[1:10]}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kInside);
  EXPECT_EQ(rhs->elements.size(), 1u);
  // Range element is a select node
  EXPECT_EQ(rhs->elements[0]->kind, ExprKind::kSelect);
}

TEST(ParserA83, InsideExprMixedValuesAndRanges) {
  auto r =
      Parse("module m; initial x = a inside {5, [10:20], 30}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kInside);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

// =============================================================================
// A.8.3 Expressions — mintypmax_expression
// =============================================================================

// § mintypmax_expression ::= expression : expression : expression

TEST(ParserA83, MinTypMaxInDelay) {
  auto r = Parse("module m;\n"
                 "  wire y;\n"
                 "  assign #(1:2:3) y = 1'b0;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § mintypmax_expression ::= expression (single form)

TEST(ParserA83, MinTypMaxSingleExpr) {
  auto r = Parse("module m;\n"
                 "  wire y;\n"
                 "  assign #5 y = 1'b0;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.3 Expressions — part_select_range / constant_part_select_range
// =============================================================================

// § part_select_range ::= constant_range

TEST(ParserA83, PartSelectConstantRange) {
  auto r = Parse("module m; initial x = data[15:8]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
  EXPECT_FALSE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
}

// § part_select_range ::= indexed_range (+:)

TEST(ParserA83, PartSelectIndexedPlus) {
  auto r = Parse("module m; initial x = data[0+:8]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
}

// § part_select_range ::= indexed_range (-:)

TEST(ParserA83, PartSelectIndexedMinus) {
  auto r = Parse("module m; initial x = data[7-:8]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_minus);
}

// =============================================================================
// A.8.3 Expressions — genvar_expression
// =============================================================================

// § genvar_expression ::= constant_expression (used in generate for)

TEST(ParserA83, GenvarExprInGenerateFor) {
  auto r = Parse("module m;\n"
                 "  genvar i;\n"
                 "  generate\n"
                 "    for (i = 0; i < 4; i = i + 1) begin : gen_blk\n"
                 "      wire w;\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.3 Expressions — module_path_expression
// =============================================================================

// § module_path_expression used in specify block path conditions

TEST(ParserA83, ModulePathExprInSpecify) {
  auto r = Parse("module m(input a, output y);\n"
                 "  specify\n"
                 "    (a => y) = 1;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § module_path_conditional_expression used in specify ifnone

TEST(ParserA83, ModulePathConditionalInSpecify) {
  auto r = Parse("module m(input a, input en, output y);\n"
                 "  specify\n"
                 "    if (en) (a => y) = 2;\n"
                 "    ifnone (a => y) = 3;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.3 Expressions — misc expression forms
// =============================================================================

// Multiple binary operators chained

TEST(ParserA83, ChainedBinaryOps) {
  auto r = Parse("module m; initial x = a | b & c ^ d; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
}

// Unary reduction operators

TEST(ParserA83, UnaryReductionAnd) {
  auto r = Parse("module m; initial x = &a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

TEST(ParserA83, UnaryReductionOr) {
  auto r = Parse("module m; initial x = |a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
}

TEST(ParserA83, UnaryReductionXor) {
  auto r = Parse("module m; initial x = ^a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kCaret);
}

// Shift operators

TEST(ParserA83, ExprLeftShift) {
  auto r = Parse("module m; initial x = a << 2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtLt);
}

TEST(ParserA83, ExprRightShift) {
  auto r = Parse("module m; initial x = a >> 2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kGtGt);
}

// Comparison operators

TEST(ParserA83, ExprEquality) {
  auto r = Parse("module m; initial x = (a == b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEq);
}

TEST(ParserA83, ExprCaseEquality) {
  auto r = Parse("module m; initial x = (a === b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEqEq);
}

// Parenthesized expression

TEST(ParserA83, ParenthesizedExpr) {
  auto r = Parse("module m; initial x = (a + b) * c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
  // LHS should be binary add (from the parens)
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPlus);
}

// Continuous assignment with expression

TEST(ParserA83, ExprInContAssign) {
  auto r = Parse("module m;\n"
                 "  wire [7:0] y;\n"
                 "  wire [7:0] a, b;\n"
                 "  assign y = a + b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstContAssignRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}
