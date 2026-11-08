#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_specify.h"

using namespace delta;

namespace {

TEST(TimingCheckCommandParsing, FullskewLimit1AndLimit2InSourceOrder) {
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
  ASSERT_NE(tc->limits[0], nullptr);
  ASSERT_NE(tc->limits[1], nullptr);
  EXPECT_EQ(tc->limits[0]->int_val, 4u);
  EXPECT_EQ(tc->limits[1]->int_val, 6u);
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

TEST(TimingCheckCommandParsing, FullskewEmptyNotifierWithFlags) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $fullskew(posedge clk1, negedge clk2, 4, 6, , 1, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kFullskew);
  EXPECT_TRUE(tc->notifier.empty());
  ASSERT_NE(tc->event_based_flag, nullptr);
  ASSERT_NE(tc->remain_active_flag, nullptr);
}

TEST(TimingCheckCommandParsing, ErrorFullskewMissingSecondLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $fullskew(posedge clk1, negedge clk2, 4);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "$fullskew requires two timing_check_limit arguments", 3,
      "31.4.3"));
}

TEST(TimingCheckCommandParsing, ErrorFullskewMissingBothLimits) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $fullskew(posedge clk1, negedge clk2);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ',', got ')'", 3, "31.2"));
}

}  // namespace
