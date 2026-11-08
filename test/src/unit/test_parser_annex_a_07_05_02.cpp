#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_specify.h"

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
  EXPECT_NE(tc->limits[0], nullptr);
  EXPECT_NE(tc->limits[1], nullptr);
}

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
  EXPECT_NE(tc->limits[1], nullptr);
}

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

TEST(TimingCheckArgumentParsing, NotifierEscapedIdentifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(d, posedge clk, 10, \\notif-1 );\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->notifier, "notif-1");
  EXPECT_EQ(tc->limits.size(), 1u);
}

TEST(TimingCheckArgumentParsing, NotifierThatIsNoIdentifierIsRejected) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(d, posedge clk, 10, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a timing check's notifier is a variable identifier", 3,
      "A.7.5.2"));
}

TEST(TimingCheckArgumentParsing, NotifierExpressionIsRejected) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk, d, 10, n + 1);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a timing check's notifier is a variable identifier", 3,
      "A.7.5.2"));
}

TEST(TimingCheckArgumentParsing, DelayedReferenceAndDataEscapedIdentifiers) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, d, 1, 2, n, , , \\d-clk , \\d-d [1]);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->delayed_ref, "d-clk");
  EXPECT_EQ(tc->delayed_ref_expr, nullptr);
  EXPECT_EQ(tc->delayed_data, "d-d");
  EXPECT_NE(tc->delayed_data_expr, nullptr);
}

TEST(TimingCheckArgumentParsing, DelayedReferenceOmittedBeforeDelayedData) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, d, 1, 2, n, , , , dD);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_TRUE(tc->delayed_ref.empty());
  EXPECT_EQ(tc->delayed_data, "dD");
}

TEST(TimingCheckArgumentParsing, DelayedReferenceThatIsNoIdentifierIsRejected) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, d, 1, 2, n, , , 5, dD);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a delayed_reference is a terminal identifier", 3, "A.7.5.2"));
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_TRUE(tc->delayed_ref.empty());
  EXPECT_EQ(tc->delayed_data, "dD");
}

TEST(TimingCheckArgumentParsing, DelayedDataThatIsNoIdentifierIsRejected) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, d, 1, 2, n, , , dCLK, 3 + 1);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "a delayed_data is a terminal identifier",
                            3, "A.7.5.2"));
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->delayed_ref, "dCLK");
  EXPECT_TRUE(tc->delayed_data.empty());
}

TEST(TimingCheckArgumentParsing, ErrorDelayedRefMissingCloseBracket) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK[1, dD);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ']', got ','", 3, "31.9"));
}

TEST(TimingCheckArgumentParsing, ParenthesizedLimitAndBareOffsetTriplesTaken) {
  auto r = Parse(
      "module m(input clk, data);\n"
      "  reg ntf;\n"
      "  specify\n"
      "    $setup(data, posedge clk, (1:2:3));\n"
      "    $setuphold(posedge clk, data, (1:2:3), (4:5:6), ntf);\n"
      "    $width(posedge clk, 10, (0:1:2), ntf);\n"
      "    $nochange(posedge clk, data, 1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(TimingCheckArgumentParsing, BareLimitAndThresholdTriplesRejected) {
  auto r = Parse(
      "module m(input clk, data);\n"
      "  reg ntf;\n"
      "  specify\n"
      "    $setup(data, posedge clk, 1:2:3);\n"
      "    $setuphold(posedge clk, data, 10, 4:5:6, ntf);\n"
      "    $width(posedge clk, 10, 0:1:2, ntf);\n"
      "  endspecify\n"
      "endmodule\n");
  for (uint32_t line : {4u, 5u, 6u}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "a timing check's limit or threshold is an "
                              "expression, so a min:typ:max triple there is "
                              "parenthesized",
                              line, "A.7.5.2"))
        << "line " << line;
  }
}

}  // namespace
