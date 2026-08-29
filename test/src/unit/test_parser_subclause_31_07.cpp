#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §31.7 owns one parser rule: an optional `&&&` condition after a timing-check
// event's terminal, in both the reference and data positions
// (ParseTimingCheck). The condition body is parsed by the general expression
// parser, so the tests below observe the §31.7-owned `&&&` branch once per
// distinct alternative drawn in Syntax 31-16 (scalar_timing_check_condition's
// six forms and the parenthesized timing_check_condition). Operator/literal
// spellings inside the condition belong to the expression grammar, not §31.7.
//
// Syntax 31-3 writes `$setup(data_event, reference_event, timing_check_limit)`,
// where Syntax 31-4 writes `$hold(reference_event, data_event, ...)`. A
// condition on a $setup's first argument therefore reaches data_condition, and
// one on a $hold's first argument reaches ref_condition.

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
  EXPECT_NE(tc->data_condition, nullptr);
}

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
  EXPECT_NE(tc->data_condition, nullptr);
}

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
  EXPECT_NE(tc->data_condition, nullptr);
}

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
  EXPECT_NE(tc->data_condition, nullptr);
}

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
  EXPECT_NE(tc->data_condition, nullptr);
}

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

// §31.7: a scalar_timing_check_condition need not be parenthesized -- the
// comparison form is a direct alternative of timing_check_condition. Exercise
// the un-parenthesized `expression == scalar_constant` production so the parser
// accepts the bare comparison in addition to the `( ... )` wrapper covered
// above.
TEST(ConditionedTimingCheckParsing, ScalarTimingCheckCondBareComparison) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& en == 1'b1, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->data_condition, nullptr);
}

// §31.7 negative form: when `&&&` is present a timing_check_condition is
// required. An empty condition -- `&&&` immediately followed by the argument
// comma -- has no expression to parse and shall be rejected.
TEST(ConditionedTimingCheckParsing, ConditionRequiredAfterAmpAmpAmp) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&&, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  // The condition body is parsed by the expression parser, so the empty
  // condition is reported by §11.2; §31.7 has no report of its own here.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"));
}

}  // namespace
