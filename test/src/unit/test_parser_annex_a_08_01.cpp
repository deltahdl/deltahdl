#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"

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
  // §30.4.5 owns the one-source, one-destination rule of the parallel path,
  // and the report stands at the '(' opening the path declaration.
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

// A.8.1 makes concatenation recursive through primary, so every operand of a
// concatenation may itself be a concatenation. This covers the case where all
// of them are; test_parser_subclause_11_04_12.cpp covers a single nested
// operand beside a scalar one.
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

// concatenation ::= { expression { , expression } } — the trailing repetition
// is optional, so a lone expression is a well-formed production.
// test_parser_subclause_11_04_12.cpp covers the same shape against the §11.4.12
// prose.
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
  // §11.4.12 owns the concatenation braces.
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
  // A multiple concatenation is likewise not a legal specify path terminal
  // (Annex A.7.2/A.7.3; §30.4.5). The parallel '=>' source must be a single
  // specify_input_terminal_descriptor, so this is rejected.
  auto r = Parse(
      "module m(input a, input b, output c);\n"
      "  specify\n"
      "    ({2{a, b}} => c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  // §30.4.5 owns the one-source, one-destination rule of the parallel path.
  EXPECT_TRUE(ReportedError(r.diags,
                            "parallel path '=>' requires a single source and "
                            "destination terminal",
                            3, "30.4.5"));
}

// A module_path_concatenation is no terminal of a full '*>' path either:
// A.7.3's list_of_path_inputs and list_of_path_outputs are comma-separated
// descriptors with no brace around them, and A.8.1's production is a
// module_path_primary (A.8.4) that stands only in the module_path_expression
// of a state-dependent path's `if`. The brace group is reported under A.7.3.
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

// The same for module_path_multiple_concatenation
// ({ constant_expression module_path_concatenation }) in the full '*>' form.
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

// Where the two productions do stand: the module_path_expression of a
// state-dependent path's `if` (A.7.2 through A.8.3 and A.8.4).
TEST(ConcatenationParsing, ModulePathConcatenationInPathCondition) {
  EXPECT_TRUE(
      ParseOk("module m(input a, input b, output y);\n"
              "  specify\n"
              "    if ({a, b}) (a => y) = 5;\n"
              "    if ({2{a}}) (b => y) = 6;\n"
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
  auto r = Parse(
      "module m;\n"
      "  initial x = {>> {}};\n"
      "endmodule\n");
  // §11.2 owns the report Parser::ParsePrimaryExpr makes for the missing
  // stream_expression; §11.4.14 states the stream_concatenation itself.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
}

// slice_size ::= simple_type | constant_expression, and the expression runs up
// to the brace opening the stream_concatenation: an operator, a conditional
// and a parenthesized operand are read whole into the slice size.
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

// stream_expression ::= expression [ with [ array_range_expression ] ], so the
// range follows the whole operand: a name, a parenthesized operand and a
// member alike. Its select begins where its first bound does, the 1 at column
// 28 of line 2.
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

// §11.4.14.4 lets the expression before a stream's `with` be any
// one-dimensional unpacked array, the queue an array locator call returns
// among them, so the operand of A.8.1's stream_expression may carry A.8.2's
// with clause of its own. The two are kept apart: the locator's parenthesized
// predicate stays its with expression and the bracketed range is the
// stream's, where one used to overwrite the other. A plain name carries the
// range alone.
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

// A.8.1 writes `with [ array_range_expression ]` in stream_expression alone.
// After a name, an array method call, a parenthesized expression, an operand
// of a plain concatenation, a call's argument or a statement's call it is
// reported where the `with` stands, and what follows it is still read.
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

// A.8.1's footnote 40 makes `{ }` the empty unpacked array concatenation of
// §10.10 alone, used in no other form of concatenation: as an item of a
// concatenation, of a multiple concatenation or of a stream it is reported
// where it stands. A nested concatenation that holds an item is left alone.
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
