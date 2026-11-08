#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"

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
  EXPECT_TRUE(ReportedError(r.diags,
                            "parallel path '=>' requires a single source and "
                            "destination terminal",
                            3, "30.4.5"));
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

TEST(ConcatenationParsing, ConcatenationNestedInEveryOperand) {
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

TEST(ConcatenationParsing, ConcatenationOneExpressionProduction) {
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
  EXPECT_TRUE(ReportedError(r.diags, "expected '}', got ';'", 2, "11.4.12"));
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
  auto r = Parse(
      "module m(input a, input b, output c);\n"
      "  specify\n"
      "    ({2{a, b}} => c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "parallel path '=>' requires a single source and "
                            "destination terminal",
                            3, "30.4.5"));
}

TEST(ConcatenationParsing, ModulePathConcatenationInFullPathIsRejected) {
  auto r = Parse(
      "module m(input a, input b, output c, output d);\n"
      "  specify\n"
      "    ({a, b} *> {c, d}) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "path terminals are listed with commas alone; a concatenation is no "
      "specify terminal",
      3, "A.7.3"));
}

TEST(ConcatenationParsing,
     ModulePathMultipleConcatenationInFullPathIsRejected) {
  auto r = Parse(
      "module m(input a, input b, output c);\n"
      "  specify\n"
      "    ({2{a, b}} *> c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "path terminals are listed with commas alone; a concatenation is no "
      "specify terminal",
      3, "A.7.3"));
}

TEST(ConcatenationParsing, ModulePathConcatenationInPathCondition) {
  EXPECT_TRUE(
      ParseOk("module m(input a, input b, output y);\n"
              "  specify\n"
              "    if ({a, b}) (a => y) = 5;\n"
              "    if ({2{a}}) (b => y) = 6;\n"
              "  endspecify\n"
              "endmodule\n"));
}

TEST(ConcatenationParsing, StreamingConcatWithParameterSliceSize) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter W = 4;\n"
              "  logic [7:0] a, b;\n"
              "  initial x = {>> W {a, b}};\n"
              "endmodule\n"));
}

TEST(ConcatenationParsing, StreamConcatenationEmptyRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial x = {>> {}};\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
}

TEST(ConcatenationParsing, StreamingSliceSizeOfAnyConstantExpression) {
  auto r = Parse(
      "module m;\n"
      "  localparam int W = 4;\n"
      "  initial begin\n"
      "    x = {<< W*2 {a}};\n"
      "    x = {<< W > 2 ? 8 : 16 {a}};\n"
      "    x = {<< (W) - 1 {a}};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  const Stmt* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->rhs->lhs->kind, ExprKind::kBinary);
  EXPECT_EQ(body->stmts[1]->rhs->lhs->kind, ExprKind::kTernary);
  EXPECT_EQ(body->stmts[2]->rhs->lhs->kind, ExprKind::kBinary);
}

TEST(ConcatenationParsing, StreamExpressionRangeFollowsTheWholeOperand) {
  auto r = Parse(
      "module m;\n"
      "  initial x = {>> {q with [1:2]}};\n"
      "  initial x = {>> {(q) with [0], p.q with [1 +: 2]}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  const auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  const Expr* range = items[0]->body->rhs->elements[0]->stream_range;
  ASSERT_NE(range, nullptr);
  EXPECT_EQ(range->kind, ExprKind::kSelect);
  EXPECT_EQ(range->range.start.line, 2u);
  EXPECT_EQ(range->range.start.column, 28u);
  const auto& operands = items[1]->body->rhs->elements;
  ASSERT_EQ(operands.size(), 2u);
  EXPECT_NE(operands[0]->stream_range, nullptr);
  EXPECT_EQ(operands[1]->kind, ExprKind::kMemberAccess);
  ASSERT_NE(operands[1]->stream_range, nullptr);
  EXPECT_TRUE(operands[1]->stream_range->is_part_select_plus);
}

TEST(ConcatenationParsing, StreamRangeKeptApartFromTheOperandsWithClause) {
  auto r = Parse(
      "module m;\n"
      "  initial x = {>> {q.find with (item > 1) with [0:1], a with [2]}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  const Expr* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->elements.size(), 2u);
  const Expr* locator = rhs->elements[0];
  ASSERT_NE(locator->with_expr, nullptr);
  EXPECT_TRUE(locator->with_has_parens);
  EXPECT_EQ(locator->with_expr->kind, ExprKind::kBinary);
  ASSERT_NE(locator->stream_range, nullptr);
  EXPECT_EQ(locator->stream_range->kind, ExprKind::kSelect);
  EXPECT_NE(locator->stream_range->index_end, nullptr);
  const Expr* name = rhs->elements[1];
  EXPECT_EQ(name->with_expr, nullptr);
  ASSERT_NE(name->stream_range, nullptr);
  EXPECT_EQ(name->stream_range->index_end, nullptr);
}

TEST(ConcatenationParsing, WithRangeOutsideAStreamExpressionRejected) {
  auto r = Parse(
      "module m;\n"
      "  int a[4], q[$], b;\n"
      "  initial begin\n"
      "    b = a with [0];\n"
      "    b = q.sum with [0 +: 2];\n"
      "    b = (a) with [1];\n"
      "    b = {a with [0], 8'd1};\n"
      "    b = f(a with [2:3]);\n"
      "    q.reverse with [1:2];\n"
      "    b = 1;\n"
      "  end\n"
      "endmodule\n");
  constexpr const char* kStrayRange =
      "a with range follows only the operand of a stream expression in a "
      "streaming concatenation";
  for (uint32_t line = 4; line <= 9; ++line) {
    EXPECT_TRUE(ReportedError(r.diags, kStrayRange, line, "A.8.1"))
        << "line " << line;
  }
  EXPECT_EQ(r.diags.size(), 6u);
}

TEST(ConcatenationParsing, EmptyConcatenationAsAnItemRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] v;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    v = {8'd1, {}};\n"
      "    v = {2{4'd1, {}}};\n"
      "    v = {>> {v, {}}};\n"
      "    q = {q, {}};\n"
      "    q = {};\n"
      "    v = {4'd1, {2'd1, 2'd2}};\n"
      "  end\n"
      "endmodule\n");
  constexpr const char* kEmptyItem =
      "an empty concatenation, {}, is the empty unpacked array concatenation "
      "and no item of another concatenation";
  for (uint32_t line = 5; line <= 8; ++line) {
    EXPECT_TRUE(ReportedError(r.diags, kEmptyItem, line, "A.8.1"))
        << "line " << line;
  }
  EXPECT_EQ(r.diags.size(), 4u);
}

}  // namespace
