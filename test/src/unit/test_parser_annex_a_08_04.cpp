#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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

TEST(PrimaryParsing, PrimaryUnbasedUnsizedLiteral1) {
  auto r = Parse("module m; initial x = '1; endmodule\n");
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

TEST(PrimaryParsing, PrimaryLiteralSizedInteger) {
  auto r = Parse("module m; initial x = 8'hFF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(PrimaryParsing, PrimaryLiteralBinary) {
  auto r = Parse("module m; initial x = 4'b1010; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(PrimaryParsing, TimeLiteralNanoseconds) {
  auto r = Parse("module m; initial #100ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, TimeLiteralPicoseconds) {
  auto r = Parse("module m; initial #50ps; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, TimeLiteralMicroseconds) {
  auto r = Parse("module m; initial #1us; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, TimeLiteralFixedPoint) {
  auto r = Parse("module m; initial #2.5ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, PrimaryUnbasedUnsizedLiteralX) {
  auto r = Parse("module m; initial x = 'x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(PrimaryParsing, PrimaryUnbasedUnsizedLiteralZ) {
  auto r = Parse("module m; initial x = 'z; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
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
  EXPECT_FALSE(ParseOk("module m; initial x = (1 + 2; endmodule\n"));
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
  EXPECT_FALSE(ParseOk("module m; initial x = a[3; endmodule\n"));
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

}  // namespace
