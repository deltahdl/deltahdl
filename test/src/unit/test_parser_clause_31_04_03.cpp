#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

TEST(TimingCheckCommandParsing, FullskewEventFlagWithoutRemainActiveFlag) {
  // The optional nesting permits event_based_flag while remain_active_flag is
  // omitted; the extended-arg parser must close out after the event flag.
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $fullskew(posedge clk1, negedge clk2, 4, 6, ntfr, 1);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kFullskew);
  EXPECT_EQ(tc->notifier, "ntfr");
  ASSERT_NE(tc->event_based_flag, nullptr);
  EXPECT_EQ(tc->remain_active_flag, nullptr);
}

TEST(TimingCheckCommandParsing, ErrorFullskewMissingSecondLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $fullskew(posedge clk1, negedge clk2, 4);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

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
