#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA81, ModulePathConcatenation) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    ({a, b} => c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA81, ConcatenationBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial x = {a, b, c};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

TEST(ParserA81, MultipleConcatenation) {
  auto r = Parse(
      "module m;\n"
      "  initial x = {3{a}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
}

TEST(ParserA81, StreamingConcatRight) {
  auto r = Parse(
      "module m;\n"
      "  initial x = {>> {a, b}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
}

TEST(ParserA81, StreamingConcatLeft) {
  auto r = Parse(
      "module m;\n"
      "  initial x = {<< {a, b}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
}

TEST(ParserA81, StreamingConcatWithSliceSize) {
  auto r = Parse(
      "module m;\n"
      "  initial x = {>> byte {a, b}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA81, StreamingConcatWithNumericSlice) {
  auto r = Parse(
      "module m;\n"
      "  initial x = {>> 8 {a, b}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA81, EmptyUnpackedArrayConcat) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA81, ConcatenationNested) {
  auto r = Parse(
      "module m;\n"
      "  initial x = {{a, b}, {c, d}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 2u);
}

TEST(ParserA81, StreamExpressionWithRange) {
  auto r = Parse(
      "module m;\n"
      "  initial x = {>> {a with [0:3]}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
