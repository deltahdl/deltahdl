#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA70503, ScalarTimingCheckCondNegation) {
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

TEST(ParserA70503, ScalarTimingCheckCondEquality) {
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

TEST(ParserA70503, ScalarTimingCheckCondInequality) {
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

TEST(ParserA70503, ScalarConstantUnsized_b0) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 'b0), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA70503, ScalarConstantUnsized_b1) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 'b1), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA70503, TimingCheckEventPosedge) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->data_terminal.name, "clk");
}

TEST(ParserA70503, TimingCheckEventNegedge) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(negedge clk, data, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
}

TEST(ParserA70503, TimingCheckEventEdgeKeyword) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kEdge);
  EXPECT_EQ(tc->data_terminal.name, "clk");
}

TEST(ParserA70503, ControlledTimingCheckEventPeriod) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(posedge clk, 50);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
}

TEST(ParserA70503, TerminalPartSelect) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data[3:0], posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_terminal.name, "data");
  EXPECT_EQ(tc->ref_terminal.range_kind, SpecifyRangeKind::kPartSelect);
  EXPECT_NE(tc->ref_terminal.range_left, nullptr);
  EXPECT_NE(tc->ref_terminal.range_right, nullptr);
}

TEST(ParserA70503, TerminalInterfaceDotPort) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(intf.data, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_terminal.interface_name, "intf");
  EXPECT_EQ(tc->ref_terminal.name, "data");
}

TEST(ParserA70503, TimingCheckConditionBare) {
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

TEST(ParserA70503, TimingCheckConditionParenthesized) {
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

TEST(TimingCheckEventNoEdge, TimingCheckEventNoEdge) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kNone);
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNone);
  EXPECT_EQ(tc->ref_terminal.name, "data");
  EXPECT_EQ(tc->data_terminal.name, "clk");
}

}
