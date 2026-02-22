// Tests for A.8.4 — Primaries — Parser

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
// A.8.4 Primaries — constant_primary
// =============================================================================

// § constant_primary — primary_literal (integer)

TEST(ParserA84, ConstantPrimaryIntegerLiteral) {
  auto r = Parse("module m; parameter int P = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *param = r.cu->modules[0]->items[0];
  ASSERT_NE(param, nullptr);
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kIntegerLiteral);
}

// § constant_primary — primary_literal (real)

TEST(ParserA84, ConstantPrimaryRealLiteral) {
  auto r = Parse("module m; parameter real R = 3.14; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kRealLiteral);
}

// § constant_primary — primary_literal (string)

TEST(ParserA84, ConstantPrimaryStringLiteral) {
  auto r = Parse("module m; parameter string S = \"hello\"; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kStringLiteral);
}

// § constant_primary — ps_parameter_identifier constant_select

TEST(ParserA84, ConstantPrimaryParameterIdentifier) {
  auto r = Parse("module m;\n"
                 "  parameter int A = 5;\n"
                 "  parameter int B = A;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *param = r.cu->modules[0]->items[1];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kIdentifier);
}

// § constant_primary — enum_identifier

TEST(ParserA84, ConstantPrimaryEnumIdentifier) {
  auto r = Parse("module m;\n"
                 "  typedef enum {RED, GREEN, BLUE} color_t;\n"
                 "  parameter color_t C = RED;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § constant_primary — constant_concatenation

TEST(ParserA84, ConstantPrimaryConcatenation) {
  auto r = Parse("module m; parameter int P = {4'd1, 4'd2}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kConcatenation);
}

// § constant_primary — constant_multiple_concatenation

TEST(ParserA84, ConstantPrimaryMultipleConcatenation) {
  auto r = Parse("module m; parameter int P = {4{4'd1}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kReplicate);
}

// § constant_primary — parenthesized constant_mintypmax_expression

TEST(ParserA84, ConstantPrimaryParenthesized) {
  auto r = Parse("module m; parameter int P = (1 + 2); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kBinary);
}

// § constant_primary — constant_cast

TEST(ParserA84, ConstantPrimaryCast) {
  auto r = Parse("module m;\n"
                 "  parameter int P = int'(3.14);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kCast);
}

// § constant_primary — type_reference

TEST(ParserA84, ConstantPrimaryTypeReference) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] x;\n"
                 "  parameter int W = $bits(x);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § constant_primary — null

TEST(ParserA84, ConstantPrimaryNull) {
  auto r = Parse("module m; initial x = null; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->text, "null");
}

// § constant_primary — constant_assignment_pattern_expression

TEST(ParserA84, ConstantPrimaryAssignmentPattern) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    automatic int arr [3] = '{1, 2, 3};\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § constant_primary — unbased_unsized_literal

TEST(ParserA84, ConstantPrimaryUnbasedUnsizedLiteral) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] x;\n"
                 "  assign x = '1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstContAssignRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

// =============================================================================
// A.8.4 Primaries — module_path_primary
// =============================================================================

// § module_path_primary — number in specify

TEST(ParserA84, ModulePathPrimaryNumber) {
  auto r = Parse("module m(input a, output b);\n"
                 "  specify\n"
                 "    (a => b) = 10;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § module_path_primary — identifier in specify

TEST(ParserA84, ModulePathPrimaryIdentifier) {
  auto r = Parse("module m(input a, input en, output b);\n"
                 "  specify\n"
                 "    if (en) (a => b) = 5;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.4 Primaries — primary
// =============================================================================

// § primary — primary_literal (integer)

TEST(ParserA84, PrimaryIntegerLiteral) {
  auto r = Parse("module m; initial x = 8'hFF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// § primary — primary_literal (real)

TEST(ParserA84, PrimaryRealLiteral) {
  auto r = Parse("module m; initial x = 3.14; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

// § primary — primary_literal (string)

TEST(ParserA84, PrimaryStringLiteral) {
  auto r = Parse("module m; initial x = \"hello\"; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

// § primary — hierarchical_identifier select

TEST(ParserA84, PrimaryHierarchicalIdentifier) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] data;\n"
                 "  logic x;\n"
                 "  initial x = data[3];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
}

// § primary — concatenation

TEST(ParserA84, PrimaryConcatenation) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] a, b;\n"
                 "  logic [15:0] c;\n"
                 "  initial c = {a, b};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
}

// § primary — multiple_concatenation

TEST(ParserA84, PrimaryMultipleConcatenation) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] a;\n"
                 "  logic [31:0] b;\n"
                 "  initial b = {4{a}};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
}

// § primary — function_subroutine_call

TEST(ParserA84, PrimaryFunctionCall) {
  auto r = Parse("module m;\n"
                 "  function int foo(int a); return a + 1; endfunction\n"
                 "  initial x = foo(5);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

// § primary — parenthesized mintypmax_expression

TEST(ParserA84, PrimaryParenthesizedExpr) {
  auto r = Parse("module m; initial x = (1 + 2); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
}

// § primary — cast

TEST(ParserA84, PrimaryCast) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] a;\n"
                 "  initial a = int'(3.14);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
}

// § primary — assignment_pattern_expression

TEST(ParserA84, PrimaryAssignmentPattern) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    automatic int arr [3] = '{0, 1, 2};\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § primary — streaming_concatenation

TEST(ParserA84, PrimaryStreamingConcat) {
  auto r = Parse("module m;\n"
                 "  logic [31:0] a;\n"
                 "  logic [31:0] b;\n"
                 "  initial b = {<< 8 {a}};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
}

// § primary — this

TEST(ParserA84, PrimaryThis) {
  auto r = Parse("module m; initial x = this; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § primary — $

TEST(ParserA84, PrimaryDollar) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] q [$];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § primary — null

TEST(ParserA84, PrimaryNull) {
  auto r = Parse("module m; initial x = null; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->text, "null");
}

// =============================================================================
// A.8.4 Primaries — class_qualifier
// =============================================================================

// § class_qualifier — class_scope

TEST(ParserA84, ClassQualifierScope) {
  auto r = Parse("module m; initial x = pkg::my_const; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
}

// =============================================================================
// A.8.4 Primaries — range_expression
// =============================================================================

// § range_expression — expression (simple index)

TEST(ParserA84, RangeExpressionSimpleIndex) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] data;\n"
                 "  logic x;\n"
                 "  initial x = data[0];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
}

// § range_expression — part_select_range

TEST(ParserA84, RangeExpressionPartSelect) {
  auto r = Parse("module m;\n"
                 "  logic [15:0] data;\n"
                 "  logic [7:0] x;\n"
                 "  initial x = data[7:0];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_NE(rhs->index_end, nullptr);
}

// =============================================================================
// A.8.4 Primaries — primary_literal
// =============================================================================

// § primary_literal — number (decimal)

TEST(ParserA84, PrimaryLiteralDecimalNumber) {
  auto r = Parse("module m; initial x = 100; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// § primary_literal — number (hex)

TEST(ParserA84, PrimaryLiteralHexNumber) {
  auto r = Parse("module m; initial x = 16'hDEAD; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// § primary_literal — number (octal)

TEST(ParserA84, PrimaryLiteralOctalNumber) {
  auto r = Parse("module m; initial x = 8'o77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// § primary_literal — number (binary)

TEST(ParserA84, PrimaryLiteralBinaryNumber) {
  auto r = Parse("module m; initial x = 4'b1010; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// § primary_literal — time_literal

TEST(ParserA84, PrimaryLiteralTimeLiteral) {
  auto r = Parse("module m; initial #10ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § primary_literal — unbased_unsized_literal

TEST(ParserA84, PrimaryLiteralUnbasedUnsized) {
  auto r = Parse("module m; initial x = '0; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

// § primary_literal — string_literal

TEST(ParserA84, PrimaryLiteralStringLiteral) {
  auto r = Parse("module m; initial x = \"world\"; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

// =============================================================================
// A.8.4 Primaries — time_literal and time_unit
// =============================================================================

// § time_literal — unsigned_number time_unit (ns)

TEST(ParserA84, TimeLiteralNs) {
  auto r = Parse("module m; initial #5ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § time_literal — unsigned_number time_unit (us)

TEST(ParserA84, TimeLiteralUs) {
  auto r = Parse("module m; initial #1us; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § time_literal — unsigned_number time_unit (ms)

TEST(ParserA84, TimeLiteralMs) {
  auto r = Parse("module m; initial #2ms; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § time_literal — unsigned_number time_unit (s)

TEST(ParserA84, TimeLiteralS) {
  auto r = Parse("module m; initial #1s; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § time_literal — unsigned_number time_unit (ps)

TEST(ParserA84, TimeLiteralPs) {
  auto r = Parse("module m; initial #100ps; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § time_literal — unsigned_number time_unit (fs)

TEST(ParserA84, TimeLiteralFs) {
  auto r = Parse("module m; initial #50fs; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § time_literal — fixed_point_number time_unit

TEST(ParserA84, TimeLiteralFixedPoint) {
  auto r = Parse("module m; initial #1.5ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.4 Primaries — implicit_class_handle
// =============================================================================

// § implicit_class_handle — this

TEST(ParserA84, ImplicitClassHandleThis) {
  auto r = Parse("module m; initial x = this; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § implicit_class_handle — super

TEST(ParserA84, ImplicitClassHandleSuper) {
  auto r = Parse("module m; initial x = super; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § implicit_class_handle — this with member access

TEST(ParserA84, ImplicitClassHandleThisMember) {
  auto r = Parse("module m; initial x = this.field; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.4 Primaries — bit_select
// =============================================================================

// § bit_select — single dimension

TEST(ParserA84, BitSelectSingleDim) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] data;\n"
                 "  logic x;\n"
                 "  initial x = data[5];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index_end, nullptr);
}

// § bit_select — multi-dimensional

TEST(ParserA84, BitSelectMultiDim) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] mem [0:3];\n"
                 "  logic [7:0] x;\n"
                 "  initial x = mem[2];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
}

// =============================================================================
// A.8.4 Primaries — select
// =============================================================================

// § select — bit_select with part_select_range

TEST(ParserA84, SelectBitWithPartSelect) {
  auto r = Parse("module m;\n"
                 "  logic [31:0] data;\n"
                 "  logic [7:0] x;\n"
                 "  initial x = data[15:8];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
}

// § select — member_identifier bit_select

TEST(ParserA84, SelectMemberBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  logic x;\n"
      "  initial x = p.a[0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.4 Primaries — nonrange_select
// =============================================================================

// § nonrange_select — simple bit_select

TEST(ParserA84, NonrangeSelectBitSelect) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] data;\n"
                 "  initial data[3] = 1'b1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.4 Primaries — constant_bit_select and constant_select
// =============================================================================

// § constant_bit_select — in packed dimension

TEST(ParserA84, ConstantBitSelectPackedDim) {
  auto r = Parse("module m; logic [7:0] data; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § constant_select — in parameter expression

TEST(ParserA84, ConstantSelectParameterExpr) {
  auto r = Parse("module m;\n"
                 "  parameter int A [4] = '{1, 2, 3, 4};\n"
                 "  parameter int B = A[2];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.4 Primaries — cast and constant_cast
// =============================================================================

// § cast — type cast in expression

TEST(ParserA84, CastInExpression) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] a;\n"
                 "  int b;\n"
                 "  initial b = int'(a);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
}

// § cast — signed cast

TEST(ParserA84, CastSigned) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] a;\n"
                 "  initial a = signed'(a);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
}

// § constant_cast — in parameter

TEST(ParserA84, ConstantCastInParam) {
  auto r = Parse("module m; parameter int P = int'(3.0); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kCast);
}

// =============================================================================
// A.8.4 Primaries — constant_let_expression
// =============================================================================

// § constant_let_expression — let declaration usage

TEST(ParserA84, ConstantLetExpression) {
  auto r = Parse("module m;\n"
                 "  let my_let(a) = a + 1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.4 Primaries — system calls as primary
// =============================================================================

// § primary — system function call

TEST(ParserA84, PrimarySystemCall) {
  auto r = Parse("module m; initial x = $clog2(16); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
}

// § primary — type_reference

TEST(ParserA84, PrimaryTypeRef) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] x;\n"
                 "  initial begin\n"
                 "    automatic int w;\n"
                 "    w = $bits(x);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.4 Primaries — escaped identifier as primary
// =============================================================================

// § primary — escaped identifier

TEST(ParserA84, PrimaryEscapedIdentifier) {
  auto r = Parse("module m;\n"
                 "  logic \\my-signal ;\n"
                 "  initial \\my-signal = 1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
