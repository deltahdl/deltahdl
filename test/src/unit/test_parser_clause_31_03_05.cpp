#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TimingCheckCommandParsing, RecoveryWithNotifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recovery(posedge rst, posedge clk, 4, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRecovery);
  EXPECT_EQ(tc->notifier, "ntfr");
}

TEST(TimingCheckCommandParsing, RecoveryAsSpecifyItem) {
  auto sp = ParseSpecifySingle(
      "module m(input rst, clk);\n"
      "  specify\n"
      "    $recovery(negedge rst, posedge clk, 6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kRecovery);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "rst");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "clk");
  ASSERT_EQ(si->timing_check.limits.size(), 1u);
}

TEST(TimingCheckCommandParsing, RecoveryLimitIsExpression) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  specparam tRec = 7;\n"
      "  $recovery(posedge rst, posedge clk, tRec);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRecovery);
  ASSERT_EQ(tc->limits.size(), 1u);
}

TEST(TimingCheckCommandParsing, ErrorRecoveryMissingLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recovery(posedge rst, posedge clk);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}
