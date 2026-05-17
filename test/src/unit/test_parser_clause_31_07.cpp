#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

TEST(ConditionedTimingCheckParsing, ScalarConstantUnsizedB0) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 'b0), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConditionedTimingCheckParsing, ScalarConstantUnsizedB1) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 'b1), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

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

TEST(ConditionedTimingCheckParsing, ScalarConstant1b0) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 1'b0), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConditionedTimingCheckParsing, ScalarConstant1B1) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 1'B1), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConditionedTimingCheckParsing, ScalarConstantDecimal1) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 1), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConditionedTimingCheckParsing, ScalarConstantDecimal0) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en != 0), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
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

TEST(ConditionedTimingCheckParsing, ScalarConstantSized1B0) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 1'B0), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConditionedTimingCheckParsing, ScalarConstantUnsizedUppercaseB0) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 'B0), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConditionedTimingCheckParsing, ScalarConstantUnsizedUppercaseB1) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 'B1), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

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

}
