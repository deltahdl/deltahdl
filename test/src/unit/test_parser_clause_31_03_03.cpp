#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §31.3.3 Syntax 31-5: `$setuphold` requires two timing_check_limits
// between the data_event and the optional notifier.
TEST(TimingCheckCommandParsing, SetupholdTwoLimits) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSetuphold);
  ASSERT_GE(tc->limits.size(), 2u);
}

// §31.3.3 Syntax 31-5: every optional argument after the notifier is
// captured, including the pair of delayed signal identifiers that the
// negative-limit form of §31.9 depends on.
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

// §31.3.3 Syntax 31-5 as a specify-block item: edge-qualified reference
// first, bare data terminal second, both limits captured.
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

// §31.3.3 Syntax 31-5: the notifier is optional and may appear without any
// of the trailing negative-timing-check arguments.
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

// §31.3.3 Syntax 31-5 requires two timing_check_limit arguments; providing
// only one is ill-formed.
TEST(TimingCheckCommandParsing, ErrorSetupholdMissingSecondLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §31.3.3 Syntax 31-5 requires two timing_check_limit arguments; omitting
// both is ill-formed.
TEST(TimingCheckCommandParsing, ErrorSetupholdMissingBothLimits) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §31.3.3 explicitly states the `$setuphold` timing check can accept
// negative limit values. A negative setup_limit must parse cleanly.
TEST(TimingCheckCommandParsing, SetupholdAcceptsNegativeSetupLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, -10, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSetuphold);
  ASSERT_GE(tc->limits.size(), 2u);
}

// §31.3.3: a negative hold_limit must parse cleanly.
TEST(TimingCheckCommandParsing, SetupholdAcceptsNegativeHoldLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, -5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_GE(tc->limits.size(), 2u);
}

// §31.3.3: both limits may be negative simultaneously.
TEST(TimingCheckCommandParsing, SetupholdAcceptsBothNegativeLimits) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, -10, -5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_GE(tc->limits.size(), 2u);
}

// §31.3.3 Table 31-3: setup_limit and hold_limit are constant expressions,
// so compound arithmetic must parse in either limit slot.
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

}  // namespace
