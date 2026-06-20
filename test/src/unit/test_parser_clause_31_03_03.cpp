#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TimingCheckCommandParsing, SetupholdFullArgs) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK, dDATA);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_GE(tc->limits.size(), 2u);
  EXPECT_EQ(tc->notifier, "ntfr");
  EXPECT_EQ(tc->delayed_ref, "dCLK");
  EXPECT_EQ(tc->delayed_data, "dDATA");
}

TEST(TimingCheckCommandParsing, SetupholdAsSpecifyItem) {
  auto sp = ParseSpecifySingle(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $setuphold(posedge clk, d, 3, 2);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kTimingCheck);
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSetuphold);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
  EXPECT_EQ(si->timing_check.data_terminal.name, "d");
  ASSERT_EQ(si->timing_check.limits.size(), 2u);
}

TEST(TimingCheckCommandParsing, SetupholdWithNotifierOnly) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSetuphold);
  ASSERT_GE(tc->limits.size(), 2u);
  EXPECT_EQ(tc->notifier, "ntfr");
  EXPECT_EQ(tc->timestamp_cond, nullptr);
  EXPECT_EQ(tc->timecheck_cond, nullptr);
  EXPECT_TRUE(tc->delayed_ref.empty());
  EXPECT_TRUE(tc->delayed_data.empty());
}

TEST(TimingCheckCommandParsing, ErrorSetupholdMissingSecondLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(TimingCheckCommandParsing, ErrorSetupholdMissingBothLimits) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(TimingCheckCommandParsing, SetupholdConstantExpressionLimits) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 5 + 5, 2 * 3);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_GE(tc->limits.size(), 2u);
}

// Syntax 31-5 productions timestamp_condition ::= mintypmax_expression and
// timecheck_condition ::= mintypmax_expression: when present, each is parsed
// into its own slot following the optional notifier.
TEST(TimingCheckCommandParsing, SetupholdConditionsArePresent) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5, ntfr, ts_c, tc_c);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->notifier, "ntfr");
  EXPECT_NE(tc->timestamp_cond, nullptr);
  EXPECT_NE(tc->timecheck_cond, nullptr);
}

// Syntax 31-5 productions delayed_reference and delayed_data each admit the
// terminal_identifier [ constant_mintypmax_expression ] alternative; the
// bracket select is captured alongside the terminal name.
TEST(TimingCheckCommandParsing, SetupholdDelayedSignalsAcceptConstantSelect) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK[3], dDATA[1]);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->delayed_ref, "dCLK");
  EXPECT_EQ(tc->delayed_data, "dDATA");
  EXPECT_NE(tc->delayed_ref_expr, nullptr);
  EXPECT_NE(tc->delayed_data_expr, nullptr);
}

// The optional trailing arguments of Syntax 31-5 nest independently: a
// timestamp_condition may be supplied while the following timecheck_condition
// is omitted, so the argument list closes right after the timestamp slot.
TEST(TimingCheckCommandParsing,
     SetupholdTimestampConditionWithoutTimecheckCondition) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5, ntfr, ts_c);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->timestamp_cond, nullptr);
  EXPECT_EQ(tc->timecheck_cond, nullptr);
  EXPECT_TRUE(tc->delayed_ref.empty());
  EXPECT_TRUE(tc->delayed_data.empty());
}

// Likewise the innermost nesting: a delayed_reference may appear without a
// trailing delayed_data, with the argument list closing after the delayed
// reference terminal.
TEST(TimingCheckCommandParsing, SetupholdDelayedReferenceWithoutDelayedData) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->delayed_ref, "dCLK");
  EXPECT_EQ(tc->delayed_ref_expr, nullptr);
  EXPECT_TRUE(tc->delayed_data.empty());
}

}  // namespace
