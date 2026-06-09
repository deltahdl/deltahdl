#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TimingCheckCommandParsing, PeriodEdgeAndTerminal) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(posedge clk, 50);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kPeriod);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
  ASSERT_GE(tc->limits.size(), 1u);
}

TEST(TimingCheckCommandParsing, PeriodNoDataSignal) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(negedge clk, 50);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kPeriod);
  EXPECT_TRUE(tc->data_terminal.name.empty());
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNone);
}

TEST(TimingCheckCommandParsing, PeriodWithNotifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(posedge clk, 50, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kPeriod);
  EXPECT_EQ(tc->notifier, "ntfr");
}

TEST(TimingCheckCommandParsing, ErrorPeriodReferenceMissingEdge) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(clk, 50);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(TimingCheckCommandParsing, PeriodEmptyNotifierSlot) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(posedge clk, 50, );\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kPeriod);
  EXPECT_TRUE(tc->notifier.empty());
}

}
