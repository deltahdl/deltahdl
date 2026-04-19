#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §31.7 Syntax 31-16: scalar_timing_check_condition `~ expression` — the
// negated-expression form parses as a ref_condition on the data event.
TEST(ConditionedTimingCheckParsing, ScalarTimingCheckCondNegation) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& ~reset, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

// §31.7 Syntax 31-16: `expression == scalar_constant` is a
// scalar_timing_check_condition form; the parser must accept it after `&&&`.
TEST(ConditionedTimingCheckParsing, ScalarTimingCheckCondEquality) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 1'b1), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

// §31.7 Syntax 31-16: `expression != scalar_constant` is the nondeterministic
// inequality form.
TEST(ConditionedTimingCheckParsing, ScalarTimingCheckCondInequality) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk &&& (mode != 1'b0), data, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

// §31.7 Syntax 31-16 scalar_constant: `'b0` — unsized lowercase binary zero.
TEST(ConditionedTimingCheckParsing, ScalarConstantUnsizedB0) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 'b0), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// §31.7 Syntax 31-16 scalar_constant: `'b1` — unsized lowercase binary one.
TEST(ConditionedTimingCheckParsing, ScalarConstantUnsizedB1) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 'b1), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// §31.7 Example 1 (first form): the plain-expression condition — a bare
// identifier after `&&&` — parses without error.
TEST(ConditionedTimingCheckParsing, TimingCheckConditionBare) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& en, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

// §31.7 Syntax 31-16: `timing_check_condition` also allows a parenthesized
// scalar_timing_check_condition — even around a plain expression.
TEST(ConditionedTimingCheckParsing, TimingCheckConditionParenthesized) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

// §31.7 Syntax 31-16: `expression === scalar_constant` — the deterministic
// case-equality form.
TEST(ConditionedTimingCheckParsing, ScalarTimingCheckCondCaseEquality) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en === 1'b1), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

// §31.7 Syntax 31-16: `expression !== scalar_constant` — the deterministic
// case-inequality form.
TEST(ConditionedTimingCheckParsing, ScalarTimingCheckCondCaseInequality) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk &&& (mode !== 1'b0), data, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

// §31.7 Syntax 31-16 scalar_constant: `1'b0` — sized lowercase binary zero.
TEST(ConditionedTimingCheckParsing, ScalarConstant1b0) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 1'b0), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// §31.7 Syntax 31-16 scalar_constant: `1'B1` — sized uppercase binary one.
TEST(ConditionedTimingCheckParsing, ScalarConstant1B1) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 1'B1), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// §31.7 Syntax 31-16 scalar_constant: plain decimal `1`.
TEST(ConditionedTimingCheckParsing, ScalarConstantDecimal1) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 1), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// §31.7 Syntax 31-16 scalar_constant: plain decimal `0`.
TEST(ConditionedTimingCheckParsing, ScalarConstantDecimal0) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en != 0), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// §31.7 Syntax 31-16: each of the two timing_check_event operands can carry
// its own `&&&` condition; both must be recorded on the timing-check node.
TEST(ConditionedTimingCheckParsing, ConditionBothEvents) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk &&& en, data &&& reset, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
  EXPECT_NE(tc->data_condition, nullptr);
}

// §31.7 Syntax 31-16: a `&&&` condition may follow any
// specify_terminal_descriptor form — including a bit-select on the event
// signal.
TEST(ConditionedTimingCheckParsing, TerminalBitSelectWithCondition) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data[0] &&& en, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_terminal.name, "data");
  EXPECT_EQ(tc->ref_terminal.range_kind, SpecifyRangeKind::kBitSelect);
  EXPECT_NE(tc->ref_condition, nullptr);
}

// §31.7 Syntax 31-16: conditions coexist with edge-qualified events and
// part-select specify_terminal_descriptors on the same timing check.
TEST(ConditionedTimingCheckParsing, EdgeTerminalPartSelectWithCondition) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk &&& en, data[3:0] &&& reset, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_terminal.name, "data");
  EXPECT_EQ(tc->data_terminal.range_kind, SpecifyRangeKind::kPartSelect);
  EXPECT_NE(tc->data_condition, nullptr);
}

// §31.7 Syntax 31-16: the `controlled_timing_check_event` form requires a
// timing_check_event_control and allows an optional `&&&` condition. A
// $period invocation with `posedge clk &&& en` covers both the edge-control
// requirement and the optional condition.
TEST(ConditionedTimingCheckParsing, ControlledTimingCheckEventWithCondition) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(posedge clk &&& en, 50);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
  EXPECT_NE(tc->ref_condition, nullptr);
}

// §31.7 Syntax 31-16 scalar_constant: `1'B0` — sized uppercase binary zero.
TEST(ConditionedTimingCheckParsing, ScalarConstantSized1B0) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 1'B0), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// §31.7 Syntax 31-16 scalar_constant: `'B0` — unsized uppercase binary zero.
TEST(ConditionedTimingCheckParsing, ScalarConstantUnsizedUppercaseB0) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 'B0), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// §31.7 Syntax 31-16 scalar_constant: `'B1` — unsized uppercase binary one.
TEST(ConditionedTimingCheckParsing, ScalarConstantUnsizedUppercaseB1) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 'B1), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// §31.7 Syntax 31-16: a `&&&` timing_check_condition composes with the
// `edge` keyword on the same timing_check_event_control — the parser
// records both the edge classification and the condition.
TEST(ConditionedTimingCheckParsing, EdgeKeywordWithCondition) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge clk &&& en, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kEdge);
  EXPECT_EQ(tc->data_terminal.name, "clk");
  EXPECT_NE(tc->data_condition, nullptr);
}

}  // namespace
