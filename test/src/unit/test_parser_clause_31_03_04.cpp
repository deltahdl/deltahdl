#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TimingCheckCommandParsing, RemovalBasic) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $removal(posedge rst, posedge clk, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRemoval);
}

TEST(TimingCheckCommandParsing, RemovalWithNotifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $removal(posedge clk, rst, 3, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRemoval);
  EXPECT_EQ(tc->notifier, "ntfr");
}

TEST(TimingCheckCommandParsing, RemovalAsSpecifyItem) {
  auto sp = ParseSpecifySingle(
      "module m(input rst, clk);\n"
      "  specify\n"
      "    $removal(negedge rst, posedge clk, 4);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kRemoval);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "rst");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "clk");
  ASSERT_EQ(si->timing_check.limits.size(), 1u);
}

TEST(TimingCheckCommandParsing, RemovalLimitIsExpression) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  specparam tRem = 3;\n"
      "  $removal(posedge rst, posedge clk, tRem);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRemoval);
  ASSERT_EQ(tc->limits.size(), 1u);
}

TEST(TimingCheckCommandParsing, ErrorRemovalMissingLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $removal(posedge rst, posedge clk);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}
