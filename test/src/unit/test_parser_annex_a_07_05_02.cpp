#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

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

// notifier ::= variable_identifier, which A.9.3 spells `simple_identifier |
// escaped_identifier`; an escaped name at the notifier's place is the
// notifier, without the backslash, and §5.6.1 ends it at the white space
// before the ')'.
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

// A notifier is a variable_identifier and nothing else: a literal where the
// notifier stands is rejected rather than read as a further limit.
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

// An expression over an identifier is no variable_identifier either.
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

// delayed_reference and delayed_data are each a terminal_identifier with an
// optional `[ constant_mintypmax_expression ]`, and a terminal_identifier is
// an escaped_identifier where written so.
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

// `[ , [ delayed_reference ] [ , [ delayed_data ] ] ]`: the delayed_reference
// may be omitted while the delayed_data behind it is given.
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

// A delayed_reference is a terminal_identifier: a literal where it stands is
// rejected at the literal, and the delayed_data behind it is still read.
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

// A delayed_data is a terminal_identifier: an expression where it stands is
// rejected at the expression.
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
  // §31.9 owns the bit-select on a delayed_reference; Parser::Expect reports
  // the missing ']' from Parser::ParseOptionalDelayedRef.
  EXPECT_TRUE(ReportedError(r.diags, "expected ']', got ','", 3, "31.9"));
}

}  // namespace
