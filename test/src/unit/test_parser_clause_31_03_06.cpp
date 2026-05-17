#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

TEST(TimingCheckCommandParsing, ErrorRecremMissingSecondLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge clk, rst, 8);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(TimingCheckCommandParsing, ErrorRecremMissingBothLimits) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge clk, rst);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

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

}
