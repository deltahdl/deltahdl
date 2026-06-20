#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TimingCheckArgumentParsing, DelayedDataWithBracketExpr) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK, dD[3]);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->delayed_data, "dD");
  EXPECT_NE(tc->delayed_data_expr, nullptr);
}

TEST(TimingCheckArgumentParsing, DelayedReferenceWithBracketExpr) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK[1:2:3], dD);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->delayed_ref, "dCLK");
  ASSERT_NE(tc->delayed_ref_expr, nullptr);
  EXPECT_EQ(tc->delayed_ref_expr->kind, ExprKind::kMinTypMax);
}

TEST(TimingCheckArgumentParsing, DelayedRefDataSimple) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK, dDATA);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->delayed_ref, "dCLK");
  EXPECT_EQ(tc->delayed_data, "dDATA");
}

TEST(TimingCheckArgumentParsing, RemainActiveFlagMinTypMax) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $timeskew(posedge clk1, posedge clk2, 5, ntfr, 1, 1:2:3);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_NE(tc->remain_active_flag, nullptr);
  EXPECT_EQ(tc->remain_active_flag->kind, ExprKind::kMinTypMax);
}

TEST(TimingCheckArgumentParsing, ControlledReferenceEvent) {
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
}

TEST(TimingCheckArgumentParsing, NotifierViaSpecifyItem) {
  auto sp = ParseSpecifySingle(
      "module m(input d, clk);\n"
      "  reg notif_reg;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 10, notif_reg);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  EXPECT_EQ(sp.sole_item->timing_check.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(sp.sole_item->timing_check.notifier, "notif_reg");
}

TEST(TimingCheckArgumentParsing, TimingCheckLimitComplexExpr) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 5 + 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->limits.size(), 1u);
  EXPECT_NE(tc->limits[0], nullptr);
}

// reference_event ::= timing_check_event (the plain, non-controlled variant).
TEST(TimingCheckArgumentParsing, ReferenceEventTimingCheckEvent) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk, data, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
}

// data_event ::= timing_check_event (an edge-qualified data event).
TEST(TimingCheckArgumentParsing, DataEventTimingCheckEvent) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, negedge data, 10, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(tc->data_terminal.name, "data");
}

// timestamp_condition ::= mintypmax_expression (sixth $setuphold argument).
TEST(TimingCheckArgumentParsing, TimestampConditionMinTypMax) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5, ntfr, 1:2:3, 4:5:6);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_NE(tc->timestamp_cond, nullptr);
  EXPECT_EQ(tc->timestamp_cond->kind, ExprKind::kMinTypMax);
}

// timecheck_condition ::= mintypmax_expression (seventh $setuphold argument).
TEST(TimingCheckArgumentParsing, TimecheckConditionMinTypMax) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5, ntfr, 1:2:3, 4:5:6);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_NE(tc->timecheck_cond, nullptr);
  EXPECT_EQ(tc->timecheck_cond->kind, ExprKind::kMinTypMax);
}

// start_edge_offset / end_edge_offset ::= mintypmax_expression ($nochange
// captures them as the two limit slots after the reference/data events).
TEST(TimingCheckArgumentParsing, NochangeStartAndEndEdgeOffset) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(posedge clk, negedge data, 5, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->limits.size(), 2u);
  EXPECT_NE(tc->limits[0], nullptr);  // start_edge_offset
  EXPECT_NE(tc->limits[1], nullptr);  // end_edge_offset
}

// threshold ::= constant_expression (third $width argument, after the limit).
TEST(TimingCheckArgumentParsing, WidthThresholdArgument) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge clk, 10, 2);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->limits.size(), 2u);
  EXPECT_NE(tc->limits[1], nullptr);  // threshold
}

// event_based_flag ::= constant_expression (fifth $timeskew argument).
TEST(TimingCheckArgumentParsing, EventBasedFlagExpression) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $timeskew(posedge clk1, posedge clk2, 5, ntfr, 1, 1:2:3);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_NE(tc->event_based_flag, nullptr);
}

TEST(TimingCheckArgumentParsing, ErrorDelayedRefMissingCloseBracket) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK[1, dD);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
