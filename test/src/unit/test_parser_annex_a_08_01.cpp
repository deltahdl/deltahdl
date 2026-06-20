#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ConcatenationParsing, ModulePathConcatenation) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    ({a, b} => c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConcatenationParsing, ConcatenationBasic) {
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

TEST(ConcatenationParsing, MultipleConcatenation) {
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

TEST(ConcatenationParsing, StreamingConcatRight) {
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

TEST(ConcatenationParsing, StreamingConcatLeft) {
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

TEST(ConcatenationParsing, StreamingConcatWithSliceSize) {
  auto r = Parse(
      "module m;\n"
      "  initial x = {>> byte {a, b}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConcatenationParsing, StreamingConcatWithTypedefSliceSize) {
  auto r = Parse(
      "typedef logic [3:0] nibble_t;\n"
      "module m;\n"
      "  initial x = {>> nibble_t {a, b}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConcatenationParsing, StreamingConcatWithNumericSlice) {
  auto r = Parse(
      "module m;\n"
      "  initial x = {>> 8 {a, b}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConcatenationParsing, EmptyUnpackedArrayConcat) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConcatenationParsing, ConcatenationNested) {
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

TEST(ConcatenationParsing, ConstantConcatenation) {
  auto r = Parse(
      "module m;\n"
      "  parameter P = {8'hAB, 8'hCD};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConcatenationParsing, ConstantMultipleConcatenation) {
  auto r = Parse(
      "module m;\n"
      "  parameter P = {2{8'hFF}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConcatenationParsing, ConcatenationSingleElement) {
  auto r = Parse(
      "module m;\n"
      "  initial x = {a};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 1u);
}

TEST(ConcatenationParsing, MultipleConcatenationMultipleInner) {
  auto r = Parse(
      "module m;\n"
      "  initial x = {3{a, b}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
  EXPECT_EQ(rhs->elements.size(), 2u);
}

TEST(ConcatenationParsing, StreamConcatenationMultipleElements) {
  auto r = Parse(
      "module m;\n"
      "  initial x = {>> {a, b, c}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

TEST(ConcatenationParsing, ErrorConcatenationMissingCloseBrace) {
  auto r = Parse(
      "module m;\n"
      "  initial x = {a, b;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConcatenationParsing, StreamExpressionWithSingleIndex) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] a;\n"
              "  initial x = {>> {a with [3]}};\n"
              "endmodule\n"));
}

TEST(ConcatenationParsing, StreamExpressionWithMsbLsbRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] a;\n"
              "  initial x = {>> {a with [3:0]}};\n"
              "endmodule\n"));
}

TEST(ConcatenationParsing, StreamExpressionWithIndexedPlusRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] a;\n"
              "  initial x = {>> {a with [0 +: 4]}};\n"
              "endmodule\n"));
}

TEST(ConcatenationParsing, StreamExpressionWithIndexedMinusRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] a;\n"
              "  initial x = {>> {a with [7 -: 4]}};\n"
              "endmodule\n"));
}

TEST(ConcatenationParsing, ModulePathMultipleConcatenation) {
  EXPECT_TRUE(
      ParseOk("module m(input a, input b, output c);\n"
              "  specify\n"
              "    ({2{a, b}} => c) = 5;\n"
              "  endspecify\n"
              "endmodule\n"));
}

}  // namespace
