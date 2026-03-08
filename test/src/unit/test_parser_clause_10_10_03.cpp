// §10.10.3

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// §10.10.3: Nested braces inside concatenation parse as inner concatenation.
TEST(ParserSection1010_3, NestedConcatInsideConcat) {
  auto r = Parse(
      "module m;\n"
      "  byte BA[2];\n"
      "  initial BA = {{4'h0, 4'h6}, {4'h0, 4'hf}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  ASSERT_EQ(rhs->elements.size(), 2u);
  EXPECT_EQ(rhs->elements[0]->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements[1]->kind, ExprKind::kConcatenation);
}

// §10.10.3: String concatenation inside outer concatenation parses.
TEST(ParserSection1010_3, StringConcatInsideConcat) {
  auto r = Parse(
      "module m;\n"
      "  string SQ[$];\n"
      "  string S1, S2;\n"
      "  initial SQ = {S1, {\"hello \", S2}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  ASSERT_EQ(rhs->elements.size(), 2u);
  EXPECT_EQ(rhs->elements[1]->kind, ExprKind::kConcatenation);
}

// §10.10.3: Typed assignment pattern as element of concatenation parses.
TEST(ParserSection1010_3, TypedAssignPatternInConcat) {
  auto r = Parse(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A9[1:9];\n"
      "  initial A9 = {A3, 4, AI3'{5, 6, 7}, 8, 9};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §10.10.3: Unpacked array concatenation as item in assignment pattern parses.
TEST(ParserSection1010_3, UnpackedArrayConcatInAssignPattern) {
  auto r = Parse(
      "module m;\n"
      "  typedef int T_QI[$];\n"
      "  T_QI jagged_array[$];\n"
      "  initial jagged_array = '{(1), T_QI'{2,3,4}, {5,6}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
