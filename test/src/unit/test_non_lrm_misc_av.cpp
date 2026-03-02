// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// § constant_primary — type_reference
TEST(ParserA84, ConstantPrimaryTypeReference) {
  auto r = Parse(
      "module m;\n"
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
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->text, "null");
}

// § constant_primary — constant_assignment_pattern_expression
TEST(ParserA84, ConstantPrimaryAssignmentPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int arr [3] = '{1, 2, 3};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § constant_primary — unbased_unsized_literal
TEST(ParserA84, ConstantPrimaryUnbasedUnsizedLiteral) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  assign x = '1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstContAssignRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnbasedUnsizedLiteral);
}

// =============================================================================
// A.8.4 Primaries — module_path_primary
// =============================================================================
// § module_path_primary — number in specify
TEST(ParserA84, ModulePathPrimaryNumber) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § module_path_primary — identifier in specify
TEST(ParserA84, ModulePathPrimaryIdentifier) {
  auto r = Parse(
      "module m(input a, input en, output b);\n"
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
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// § primary — primary_literal (real)
TEST(ParserA84, PrimaryRealLiteral) {
  auto r = Parse("module m; initial x = 3.14; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

// § primary — primary_literal (string)
TEST(ParserA84, PrimaryStringLiteral) {
  auto r = Parse("module m; initial x = \"hello\"; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

// § primary — hierarchical_identifier select
TEST(ParserA84, PrimaryHierarchicalIdentifier) {
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

// § primary — concatenation
TEST(ParserA84, PrimaryConcatenation) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  logic [15:0] c;\n"
      "  initial c = {a, b};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
}

// § primary — multiple_concatenation
TEST(ParserA84, PrimaryMultipleConcatenation) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial b = {4{a}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
}

// § primary — function_subroutine_call
TEST(ParserA84, PrimaryFunctionCall) {
  auto r = Parse(
      "module m;\n"
      "  function int foo(int a); return a + 1; endfunction\n"
      "  initial x = foo(5);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

// § primary — parenthesized mintypmax_expression
TEST(ParserA84, PrimaryParenthesizedExpr) {
  auto r = Parse("module m; initial x = (1 + 2); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
}

// § primary — cast
TEST(ParserA84, PrimaryCast) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = int'(3.14);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
}

}  // namespace
