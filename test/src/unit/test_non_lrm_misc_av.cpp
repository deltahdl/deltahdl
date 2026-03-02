// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

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
