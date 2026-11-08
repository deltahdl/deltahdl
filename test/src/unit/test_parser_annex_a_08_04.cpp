#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

TEST(PrimaryParsing, PrimaryNull) {
  auto r = Parse("module m; initial x = null; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->text, "null");
}

TEST(PrimaryParsing, BitSelectMultiDim) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] mem [0:3];\n"
      "  logic [7:0] x;\n"
      "  initial x = mem[2];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
}

TEST(PrimaryParsing, ChainedBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] mem [0:3][0:1];\n"
      "  logic [7:0] x;\n"
      "  initial x = mem[2][1];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
}

TEST(PrimaryParsing, SelectMemberBitSelect) {
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

TEST(PrimaryParsing, ModulePathPrimaryNumber) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, ModulePathPrimaryIdentifier) {
  auto r = Parse(
      "module m(input a, input en, output b);\n"
      "  specify\n"
      "    if (en) (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, PrimaryHierarchicalIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  logic x;\n"
      "  initial x = data[3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
}

TEST(PrimaryParsing, PrimaryParenthesizedExpr) {
  auto r = Parse("module m; initial x = (1 + 2); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
}

TEST(PrimaryParsing, PrimaryLiteralInteger) {
  auto r = Parse("module m; initial x = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(PrimaryParsing, PrimaryLiteralString) {
  auto r = Parse("module m; initial x = \"hello\"; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

TEST(PrimaryParsing, PrimaryLiteralReal) {
  auto r = Parse("module m; initial x = 3.14; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(PrimaryParsing, PrimaryUnbasedUnsizedLiteral0) {
  auto r = Parse("module m; initial x = '0; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(PrimaryParsing, PrimaryDollarSign) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial x = q[$];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, PrimaryConcatenationWithRange) {
  auto r = Parse("module m; initial x = {a, b}[3:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, MultiConcatenationWithRange) {
  auto r = Parse("module m; initial x = {2{a}}[3:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, FunctionCallWithRange) {
  auto r = Parse(
      "module m;\n"
      "  function logic [7:0] get(); return 8'hFF; endfunction\n"
      "  initial x = get()[3:0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, FunctionCallWithBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  function logic [7:0] get(); return 8'hFF; endfunction\n"
      "  initial x = get()[0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, ImplicitClassHandleSuper) {
  auto r = Parse(
      "class C extends B;\n"
      "  function void f();\n"
      "    super.x = 1;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, ImplicitClassHandleThisDotSuper) {
  auto r = Parse(
      "class C extends B;\n"
      "  function void f();\n"
      "    this.super.x = 1;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, TimeLiteralNanoseconds) {
  auto r = Parse("module m; initial #100ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, TimeLiteralFixedPoint) {
  auto r = Parse("module m; initial #2.5ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, PrimaryStreamingConcatenation) {
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] x;\n"
      "  logic [7:0] a, b;\n"
      "  initial x = {>> {a, b}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
}

TEST(PrimaryParsing, PrimaryTypeReference) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial if (type(a) == type(logic [7:0])) x = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, ConstantPrimarySpecparam) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    specparam tPD = 5;\n"
      "    (a => b) = tPD;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, ConstantPrimaryGenvar) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : gen\n"
      "    wire [i:0] w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, ClassQualifierPackageScope) {
  auto r = Parse(
      "package pkg;\n"
      "  parameter int C = 42;\n"
      "endpackage\n"
      "module m;\n"
      "  initial x = pkg::C;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, ConstantPrimaryPackageScopedEnumIdentifier) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef enum { COLOR_RED, COLOR_GREEN, COLOR_BLUE } color_t;\n"
      "endpackage\n"
      "module m;\n"
      "  initial x = pkg::COLOR_GREEN;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, SelectChainedMemberAccess) {
  auto r = Parse(
      "module m;\n"
      "  initial x = a.b.c[0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, SelectMemberWithPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  initial x = a.b[7:4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, NonrangeSelectMemberAccess) {
  auto r = Parse(
      "module m;\n"
      "  initial x = a.b[0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, ModulePathPrimaryParenthesizedMintypMax) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = (1:2:3);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, ErrorUnclosedParenthesizedExpr) {
  auto r = Parse("module m; initial x = (1 + 2; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 1, "11.5"));
}

TEST(PrimaryParsing, PrimaryThis) {
  auto r = Parse("module m; initial x = this; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, ImplicitClassHandleThisMember) {
  auto r = Parse("module m; initial x = this.field; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, ConstantPrimaryEnumIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  parameter color_t C = RED;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, ConstantPrimaryParenthesized) {
  auto r = Parse("module m; parameter int P = (1 + 2); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kBinary);
}

TEST(PrimaryParsing, ErrorUnclosedBitSelect) {
  auto r = Parse("module m; initial x = a[3; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ']', got ';'", 1, "11.5.1"));
}

TEST(PrimaryParsing, PrimaryAssignmentPattern) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { int a; int b; } pair_t;\n"
              "  pair_t p;\n"
              "  initial p = '{1, 2};\n"
              "endmodule\n"));
}

TEST(PrimaryParsing, PrimaryLetExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let max2(a, b) = (a > b) ? a : b;\n"
              "  int x;\n"
              "  initial x = max2(3, 5);\n"
              "endmodule\n"));
}

TEST(PrimaryParsing, PrimaryValueCast) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  initial x = int'(3.5);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
  EXPECT_EQ(rhs->text, "int");
}

TEST(PrimaryParsing, ConstantPrimaryConstantCast) {
  auto r = Parse("module m; parameter int P = shortint'(3); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kCast);
  EXPECT_EQ(param->init_expr->text, "shortint");
}

TEST(PrimaryParsing, ErrorCastMissingCloseParen) {
  auto r = Parse("module m; initial x = int'(3; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 1, "6.24.1"));
}

TEST(PrimaryParsing, ErrorClassNewAsSubroutineArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial q.push_back(new(7));\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "'new' is not an expression", 2, "A.8.4"));
}

TEST(PrimaryParsing, ErrorDynamicArrayNewAsFunctionArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial x = f(1, new[3]);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "'new' is not an expression", 2, "A.8.4"));
}

TEST(PrimaryParsing, MethodCalledOnSystemFunctionResult) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $sformatf(\"%s\", s).len();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kMemberAccess);
  ASSERT_NE(rhs->lhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->lhs->kind, ExprKind::kSystemCall);
}

TEST(PrimaryParsing, MethodCallOnConcatenation) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial n = {s, \" x\"}.len();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->kind, ExprKind::kCall);
  ASSERT_NE(rhs->lhs, nullptr);
  ASSERT_EQ(rhs->lhs->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(rhs->lhs->rhs->text, "len");
  EXPECT_EQ(rhs->lhs->lhs->kind, ExprKind::kConcatenation);
}

TEST(PrimaryParsing, MethodCallOnReplication) {
  auto r = Parse(
      "module m;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial n = {3{s}}.len();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->kind, ExprKind::kCall);
  ASSERT_NE(rhs->lhs, nullptr);
  ASSERT_EQ(rhs->lhs->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(rhs->lhs->rhs->text, "len");
  EXPECT_EQ(rhs->lhs->lhs->kind, ExprKind::kReplicate);
}

TEST(PrimaryParsing, ACastThroughUnitScopeIsACast) {
  auto r = Parse(
      "typedef logic [3:0] T;\n"
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic [3:0] y;\n"
      "  initial y = $unit::T'(x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kMemberAccess);
  EXPECT_TRUE(rhs->rhs->is_scope_resolution);
  ASSERT_NE(rhs->rhs->lhs, nullptr);
  EXPECT_EQ(rhs->rhs->lhs->text, "$unit");
  ASSERT_NE(rhs->rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->rhs->text, "T");
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->text, "x");
}

TEST(PrimaryParsing, ErrorBracketAfterAPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a [0:3];\n"
      "  logic [3:0][7:0] v;\n"
      "  logic x;\n"
      "  logic [1:0] y;\n"
      "  initial begin\n"
      "    x = v[3:2][1];\n"
      "    y = a[1:2][0];\n"
      "    y = v[0+:2][1];\n"
      "    y = v[1][3:2];\n"
      "  end\n"
      "endmodule\n");
  constexpr std::string_view kMessage =
      "a part-select ends a select; no bracket follows it";
  for (uint32_t line : {7u, 8u, 9u}) {
    EXPECT_TRUE(ReportedError(r.diags, kMessage, line, "A.8.4")) << line;
  }
  EXPECT_FALSE(ReportedError(r.diags, kMessage, 10, "A.8.4"));
}

TEST(PrimaryParsing, ErrorSecondBracketAfterACall) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [7:0] row_t [0:3];\n"
      "  function row_t get(); return '{default: 8'hA5}; endfunction\n"
      "  logic x;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    x = get()[1][0];\n"
      "    x = $past(get())[1][0];\n"
      "    b = get()[1];\n"
      "    x = get()[3:0];\n"
      "  end\n"
      "endmodule\n");
  constexpr std::string_view kMessage =
      "a subroutine call's result takes one select; this is a second";
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 7, "A.8.4"));
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 8, "A.8.4"));
  EXPECT_FALSE(ReportedError(r.diags, kMessage, 9, "A.8.4"));
  EXPECT_FALSE(ReportedError(r.diags, kMessage, 10, "A.8.4"));
}

TEST(PrimaryParsing, ErrorLocalQualifierOutsideAnInlineConstraintBlock) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  int y;\n"
      "  constraint lim { x < local::y; }\n"
      "  function void f();\n"
      "    int z = local::y;\n"
      "    void'(randomize() with { x < local::y; });\n"
      "  endfunction\n"
      "endclass\n");
  constexpr std::string_view kMessage =
      "the 'local::' qualifier stands only in an inline constraint block";
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 4, "A.8.4"));
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 6, "A.8.4"));
  EXPECT_FALSE(ReportedError(r.diags, kMessage, 7, "A.8.4"));
}

TEST(PrimaryParsing, ErrorLocalQualifierInAnUnclosedConstraintBlock) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint lim { x < local::y;\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "the 'local::' qualifier stands only in an inline constraint block", 3,
      "A.8.4"));
}

}  // namespace
