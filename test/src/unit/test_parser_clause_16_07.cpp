#include "fixture_parser.h"

using namespace delta;

namespace {

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

TEST(SequenceExpressionParsing, SequenceConcatDelay) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a ##2 b ##3 c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(SequenceExpressionParsing, RangedRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a ##[1:5] b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(SequenceExpressionParsing, UnboundedDelayRange) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ##[0:$] ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(SequenceExpressionParsing, ZeroDelayConcatenation) {
  // §16.7: ##0 indicates same clock tick.
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a ##0 b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(SequenceExpressionParsing, UnboundedStarShorthandParses) {
  // §16.7: ##[*] is equivalent to ##[0:$].
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ##[*] ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(SequenceExpressionParsing, UnboundedPlusShorthandParses) {
  // §16.7: ##[+] is equivalent to ##[1:$].
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ##[+] ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(SequenceExpressionParsing, BooleanAndOrIntersectAlternativesParse) {
  // §16.7 sequence_expr: `and`, `or`, and `intersect` are first-class
  // composition operators alongside concatenation.
  auto r = Parse(
      "module m;\n"
      "  sequence s_and;\n"
      "    @(posedge clk) a and b;\n"
      "  endsequence\n"
      "  sequence s_or;\n"
      "    @(posedge clk) a or b;\n"
      "  endsequence\n"
      "  sequence s_intersect;\n"
      "    @(posedge clk) a intersect b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, FirstMatchAndThroughoutWithinParse) {
  // §16.7 sequence_expr: `first_match(...)`, `throughout`, `within`
  // alternatives are syntactic forms the parser must accept inside a
  // sequence body.
  auto r = Parse(
      "module m;\n"
      "  sequence s_fm;\n"
      "    @(posedge clk) first_match(a ##1 b);\n"
      "  endsequence\n"
      "  sequence s_th;\n"
      "    @(posedge clk) a throughout (b ##1 c);\n"
      "  endsequence\n"
      "  sequence s_wi;\n"
      "    @(posedge clk) (a ##1 b) within (c ##1 d ##1 e);\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, ConsecutiveRepetitionAbbreviationsParse) {
  // §16.7 consecutive_repetition: `[*N]`, `[*]`, `[+]` shapes following a
  // Boolean expression inside a sequence body.
  auto r = Parse(
      "module m;\n"
      "  sequence s_count;\n"
      "    @(posedge clk) a[*3];\n"
      "  endsequence\n"
      "  sequence s_star;\n"
      "    @(posedge clk) a[*];\n"
      "  endsequence\n"
      "  sequence s_plus;\n"
      "    @(posedge clk) a[+];\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, GotoAndNonconsecutiveRepetitionParse) {
  // §16.7 goto_repetition (`[->N]`) and nonconsecutive_repetition (`[=N]`).
  auto r = Parse(
      "module m;\n"
      "  sequence s_goto;\n"
      "    @(posedge clk) a[->2] ##1 b;\n"
      "  endsequence\n"
      "  sequence s_nonc;\n"
      "    @(posedge clk) a[=3] ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, SequenceMatchItemListParses) {
  // §16.7 sequence_match_item: the parenthesized form
  // `( sequence_expr { , sequence_match_item } )` lets the body interleave
  // operator_assignment / inc_or_dec / subroutine_call between matches.
  auto r = Parse(
      "module m;\n"
      "  int lv;\n"
      "  sequence s;\n"
      "    @(posedge clk) (a ##1 b, lv = 1, lv++);\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, ParenthesizedSequenceWithAbbrevParses) {
  // §16.7 sequence_abbrev applies to a parenthesized sequence_expr.
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) (a ##1 b)[*2];\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, InvertedDelayRangeIsError) {
  // §16.7 S6: when the cycle_delay_range is specified with two
  // constant_expression bounds, the upper bound must be at least the lower
  // bound. The parser-level checker catches the literal-bounds case.
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##[5:1] b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

TEST(SequenceExpressionParsing, NegativeDelayRangeBoundIsError) {
  // §16.7 S2: bounds in cycle_delay_const_range_expression may only be 0
  // or greater; a literal negative lower bound is flagged at parse time.
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##[-1:5] b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

TEST(SequenceExpressionParsing, NegativeUpperDelayRangeBoundIsError) {
  // §16.7 S2: the >=0 rule applies to the upper bound as well as the lower
  // one; a literal negative on the second expression of ##[lo:hi] is flagged
  // at parse time, exercising the hi-negative arm alongside the lo-negative
  // case above.
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##[1:-1] b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

TEST(SequenceExpressionParsing, EqualDelayRangeBoundsIsAccepted) {
  // §16.7 S6 boundary: the upper bound is permitted to equal the lower
  // bound (both inclusive).
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##[3:3] b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, MinTypMaxCycleDelayValueIsError) {
  // §16.7: a cycle_delay_range's constant_primary may not be a
  // constant_mintypmax_expression (a min:typ:max triple) that is not also a
  // plain constant_expression. `## (1:2:3)` builds the §11.11 triple in the
  // delay position and must be rejected.
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##(1:2:3) b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

TEST(SequenceExpressionParsing, ParenthesizedConditionalCycleDelayIsAccepted) {
  // §16.7 negative-of-the-negative: a parenthesized constant_expression in the
  // delay position is legal even when it contains the ':' of a `?:`
  // conditional, which must not be mistaken for a min:typ:max separator.
  auto r = Parse(
      "module m;\n"
      "  parameter SEL = 1;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##(SEL ? 1 : 2) b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, MinTypMaxCycleDelayWithParamOperandsIsError) {
  // §16.7: the min:typ:max ban on a cycle_delay_range constant_primary is
  // about the `a:b:c` shape, not the operand kind — so the §11.11 triple
  // formed from named parameters (its canonical real-world spelling) is
  // rejected just like a literal triple. This drives the §11.11 dependency's
  // real source syntax into the delay position and observes the parser
  // applying the rule.
  auto r = Parse(
      "module m;\n"
      "  parameter MIN_D = 1, TYP_D = 2, MAX_D = 3;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##(MIN_D:TYP_D:MAX_D) b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

TEST(SequenceExpressionParsing, ParenthesizedParamCycleDelayIsAccepted) {
  // §16.7 positive control for the parameter operand form: a single
  // parenthesized parameter is an ordinary constant_expression delay, not a
  // min:typ:max triple, so it must be accepted. This isolates the triple —
  // not the parameter operand — as the cause of the rejection above.
  auto r = Parse(
      "module m;\n"
      "  parameter DLY = 2;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##(DLY) b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, RealLiteralCycleDelayValueIsError) {
  // §16.7 C1: the constant_primary of a `## delay` shall result in an integer
  // value; a real literal never does and is rejected at parse time.
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##2.5 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

TEST(SequenceExpressionParsing, StringLiteralCycleDelayValueIsError) {
  // §16.7 C1: a string literal is likewise not an integer value and is
  // rejected as a cycle-delay operand.
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##\"two\" b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

TEST(SequenceExpressionParsing, IntegerLiteralCycleDelayValueIsAccepted) {
  // §16.7 C1 positive control: a plain integer literal delay is a legal
  // constant_primary, so the integer-value check must not flag it.
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##7 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SequenceExpressionParsing, ExpressionOrDistInsideSequenceParses) {
  // §16.7 expression_or_dist: a Boolean operand may be paired with a `dist`
  // clause inside a sequence body.
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    @(posedge clk) (a dist {0 := 80, 1 := 20}) |-> b;\n"
      "  endproperty\n"
      "  assert property (p);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
