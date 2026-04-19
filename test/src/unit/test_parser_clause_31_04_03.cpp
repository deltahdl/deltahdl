#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §31.4.3 Syntax 31-11: the two positional limits plus edge-qualified
// reference and data events must round-trip through the parser.
TEST(TimingCheckCommandParsing, FullskewTwoLimits) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $fullskew(posedge clk1, negedge clk2, 4, 6);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kFullskew);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk1");
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(tc->data_terminal.name, "clk2");
  ASSERT_EQ(tc->limits.size(), 2u);
}

// §31.4.3 Table 31-9: the optional notifier slot resolves to a variable
// identifier alongside the edge-qualified events and two limits.
TEST(TimingCheckCommandParsing, FullskewWithNotifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $fullskew(posedge clk1, negedge clk2, 4, 6, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kFullskew);
  EXPECT_EQ(tc->notifier, "ntfr");
  EXPECT_EQ(tc->event_based_flag, nullptr);
  EXPECT_EQ(tc->remain_active_flag, nullptr);
}

// §31.4.3 Syntax 31-11 / Table 31-9: the two trailing optional slots —
// event_based_flag and remain_active_flag — capture as expressions on the
// AST node past the notifier.
TEST(TimingCheckCommandParsing, FullskewWithEventAndRemainFlags) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $fullskew(posedge clk1, negedge clk2, 4, 6, ntfr, 1, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kFullskew);
  EXPECT_EQ(tc->notifier, "ntfr");
  ASSERT_NE(tc->event_based_flag, nullptr);
  ASSERT_NE(tc->remain_active_flag, nullptr);
}

// §31.4.3 Table 31-9: each limit is a non-negative constant expression, so
// specparam references in the limit slots must parse.
TEST(TimingCheckCommandParsing, FullskewLimitsAreExpressions) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  specparam tLo = 4;\n"
      "  specparam tHi = 6;\n"
      "  $fullskew(posedge clk1, negedge clk2, tLo, tHi);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kFullskew);
  ASSERT_EQ(tc->limits.size(), 2u);
}

// §31.4.3: zero is a valid non-negative constant and names the boundary
// case for simultaneous transitions; both limits must accept zero.
TEST(TimingCheckCommandParsing, FullskewZeroLimits) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $fullskew(posedge clk1, negedge clk2, 0, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kFullskew);
  ASSERT_EQ(tc->limits.size(), 2u);
}

// §31.4.3 Syntax 31-11 requires two positional limits; providing only one
// is ill-formed.
TEST(TimingCheckCommandParsing, ErrorFullskewMissingSecondLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $fullskew(posedge clk1, negedge clk2, 4);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §31.4.3 Syntax 31-11 requires the two positional limits; omitting both
// is ill-formed.
TEST(TimingCheckCommandParsing, ErrorFullskewMissingBothLimits) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $fullskew(posedge clk1, negedge clk2);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
