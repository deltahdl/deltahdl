#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ConcatenationParsing, ModulePathConcatenation) {
  // A concatenation is NOT a legal specify path terminal. Per Annex A.7.2/A.7.3
  // a parallel path is
  //   ( specify_input_terminal_descriptor => specify_output_terminal_descriptor
  //   )
  // and specify_input_terminal_descriptor ::= input_identifier
  // [ [ constant_range_expression ] ] — module_path_concatenation appears only
  // in module_path_primary (A.8.4), never as a path terminal. §30.4.5 also
  // states a parallel '=>' connection joins one source to one destination. So
  // this must be rejected.
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    ({a, b} => c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
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
  // A multiple concatenation is likewise not a legal specify path terminal
  // (Annex A.7.2/A.7.3; §30.4.5). The parallel '=>' source must be a single
  // specify_input_terminal_descriptor, so this is rejected.
  EXPECT_FALSE(
      ParseOk("module m(input a, input b, output c);\n"
              "  specify\n"
              "    ({2{a, b}} => c) = 5;\n"
              "  endspecify\n"
              "endmodule\n"));
}

// Positive observation of the module_path_concatenation production. The
// parallel '=>' form forbids a brace-grouped terminal list, but the full '*>'
// connection accepts terminal lists, so the concatenation syntax is consumed
// here rather than rejected.
TEST(ConcatenationParsing, ModulePathConcatenationInFullPath) {
  EXPECT_TRUE(
      ParseOk("module m(input a, input b, output c, output d);\n"
              "  specify\n"
              "    ({a, b} *> {c, d}) = 5;\n"
              "  endspecify\n"
              "endmodule\n"));
}

// Positive observation of the module_path_multiple_concatenation production
// ({ constant_expression module_path_concatenation }) in the same full '*>'
// context that admits a terminal list.
TEST(ConcatenationParsing, ModulePathMultipleConcatenationInFullPath) {
  EXPECT_TRUE(
      ParseOk("module m(input a, input b, output c);\n"
              "  specify\n"
              "    ({2{a, b}} *> c) = 5;\n"
              "  endspecify\n"
              "endmodule\n"));
}

// slice_size ::= simple_type | constant_expression. The constant_expression
// alternative is exercised as a numeric literal by
// StreamingConcatWithNumericSlice above; here it is a named parameter, the
// other constant form admitted in this position. The parser accepts an
// identifier ahead of the stream's inner brace.
TEST(ConcatenationParsing, StreamingConcatWithParameterSliceSize) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter W = 4;\n"
              "  logic [7:0] a, b;\n"
              "  initial x = {>> W {a, b}};\n"
              "endmodule\n"));
}

// Negative form of stream_concatenation ::= { stream_expression
// { , stream_expression } }: the inner brace list must hold at least one
// stream_expression, so an empty stream body is rejected.
TEST(ConcatenationParsing, StreamConcatenationEmptyRejected) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  initial x = {>> {}};\n"
              "endmodule\n"));
}

}  // namespace
