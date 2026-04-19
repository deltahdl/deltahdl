#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Moved from A.7.5.1: §31.3.6 Syntax 31-8 with the two required limits and no
// trailing optional arguments.
TEST(TimingCheckCommandParsing, RecremBasic) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge rst, posedge clk, 10, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRecrem);
  ASSERT_GE(tc->limits.size(), 2u);
}

// Moved from A.7.5.1: every optional argument after the notifier — including
// the trailing pair of delayed signal identifiers §31.9 relies on — is
// captured on the AST node.
TEST(TimingCheckCommandParsing, RecremFullArgs) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge clk, rst, 8, 3, ntfr, , , dCLK, dRST);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRecrem);
  ASSERT_GE(tc->limits.size(), 2u);
  EXPECT_EQ(tc->notifier, "ntfr");
  EXPECT_EQ(tc->delayed_ref, "dCLK");
  EXPECT_EQ(tc->delayed_data, "dRST");
}

// Moved from A.7.5.1: §31.3.6 Syntax 31-8 as a specify-block item with
// edge-qualified reference first and bare data terminal second, both limits
// captured.
TEST(TimingCheckCommandParsing, RecremAsSpecifyItem) {
  auto sp = ParseSpecifySingle(
      "module m(input rst, clk);\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, 5, 3);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kRecrem);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
  EXPECT_EQ(si->timing_check.data_terminal.name, "rst");
  ASSERT_EQ(si->timing_check.limits.size(), 2u);
}

// Moved from A.7.5.1: §31.3.6 Syntax 31-8 permits the notifier to appear
// without any of the trailing negative-timing-check arguments.
TEST(TimingCheckCommandParsing, RecremWithNotifierOnly) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge clk, rst, 8, 3, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRecrem);
  ASSERT_GE(tc->limits.size(), 2u);
  EXPECT_EQ(tc->notifier, "ntfr");
  EXPECT_EQ(tc->timestamp_cond, nullptr);
  EXPECT_EQ(tc->timecheck_cond, nullptr);
  EXPECT_TRUE(tc->delayed_ref.empty());
  EXPECT_TRUE(tc->delayed_data.empty());
}

// §31.3.6 Syntax 31-8 requires two timing_check_limit arguments; providing
// only one is ill-formed.
TEST(TimingCheckCommandParsing, ErrorRecremMissingSecondLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge clk, rst, 8);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §31.3.6 Syntax 31-8 requires two timing_check_limit arguments; omitting
// both is ill-formed.
TEST(TimingCheckCommandParsing, ErrorRecremMissingBothLimits) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge clk, rst);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §31.3.6 explicitly states the `$recrem` timing check can accept negative
// limit values. A negative recovery_limit must parse cleanly.
TEST(TimingCheckCommandParsing, RecremAcceptsNegativeRecoveryLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge clk, rst, -8, 3);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRecrem);
  ASSERT_GE(tc->limits.size(), 2u);
}

// §31.3.6: a negative removal_limit must parse cleanly.
TEST(TimingCheckCommandParsing, RecremAcceptsNegativeRemovalLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge clk, rst, 8, -3);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_GE(tc->limits.size(), 2u);
}

// §31.3.6 Table 31-6: recovery_limit and removal_limit are constant
// expressions, so compound arithmetic must parse in either limit slot.
TEST(TimingCheckCommandParsing, RecremConstantExpressionLimits) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge clk, rst, 4 + 4, 2 * 3);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_GE(tc->limits.size(), 2u);
}

}  // namespace
