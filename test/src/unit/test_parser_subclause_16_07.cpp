#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

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
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a ##0 b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(SequenceExpressionParsing, UnboundedStarShorthandParses) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ##[*] ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(SequenceExpressionParsing, UnboundedPlusShorthandParses) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ##[+] ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(SequenceExpressionParsing, BooleanAndOrIntersectAlternativesParse) {
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
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##[5:1] b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "cycle-delay range upper bound must be at least the lower bound",
      3, "16.7"));
}

TEST(SequenceExpressionParsing, NegativeDelayRangeBoundIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##[-1:5] b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "cycle-delay range bounds cannot be negative", 3, "16.7"));
}

TEST(SequenceExpressionParsing, NegativeUpperDelayRangeBoundIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##[1:-1] b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "cycle-delay range bounds cannot be negative", 3, "16.7"));
}

TEST(SequenceExpressionParsing, EqualDelayRangeBoundsIsAccepted) {
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
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##(1:2:3) b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags,
      "a min:typ:max expression may not be used as a cycle-delay value", 3,
      "16.7"));
}

TEST(SequenceExpressionParsing, ParenthesizedConditionalCycleDelayIsAccepted) {
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
  auto r = Parse(
      "module m;\n"
      "  parameter MIN_D = 1, TYP_D = 2, MAX_D = 3;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##(MIN_D:TYP_D:MAX_D) b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags,
      "a min:typ:max expression may not be used as a cycle-delay value", 4,
      "16.7"));
}

TEST(SequenceExpressionParsing, ParenthesizedParamCycleDelayIsAccepted) {
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
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##2.5 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, "cycle-delay value must be an integer", 3,
                            "16.7"));
}

TEST(SequenceExpressionParsing, StringLiteralCycleDelayValueIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##\"two\" b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, "cycle-delay value must be an integer", 3,
                            "16.7"));
}

TEST(SequenceExpressionParsing, IntegerLiteralCycleDelayValueIsAccepted) {
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
