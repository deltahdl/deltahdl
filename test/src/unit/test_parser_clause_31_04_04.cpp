#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TimingCheckCommandParsing, WidthWithThreshold) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge clk, 20, 1, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kWidth);
  ASSERT_GE(tc->limits.size(), 2u);
  EXPECT_EQ(tc->notifier, "ntfr");
}

TEST(TimingCheckCommandParsing, WidthEdgeAndTerminal) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge clk, 20);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kWidth);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
  ASSERT_GE(tc->limits.size(), 1u);
}

TEST(TimingCheckCommandParsing, WidthNoDataSignal) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge clk, 20, 1);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kWidth);
  EXPECT_TRUE(tc->data_terminal.name.empty());
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNone);
}

TEST(TimingCheckCommandParsing, ThresholdExpression) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge clk, 20, 1);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_GE(tc->limits.size(), 2u);
  EXPECT_NE(tc->limits[1], nullptr);
}

TEST(TimingCheckCommandParsing, WidthDefaultThresholdOmitted) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge clk, 20);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kWidth);
  ASSERT_EQ(tc->limits.size(), 1u);
  EXPECT_TRUE(tc->notifier.empty());
}

TEST(TimingCheckCommandParsing, ErrorWidthReferenceMissingEdge) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(clk, 20);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}
