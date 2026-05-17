#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TimingCheckCommandParsing, SkewBasic) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(posedge clk1, negedge clk2, 3);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSkew);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk1");
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(tc->data_terminal.name, "clk2");
  ASSERT_EQ(tc->limits.size(), 1u);
  EXPECT_TRUE(tc->notifier.empty());
}

TEST(TimingCheckCommandParsing, SkewWithNotifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(posedge clk1, negedge clk2, 3, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSkew);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk1");
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(tc->data_terminal.name, "clk2");
  EXPECT_EQ(tc->notifier, "ntfr");
}

TEST(TimingCheckCommandParsing, SkewAsSpecifyItem) {
  auto sp = ParseSpecifySingle(
      "module m(input clk1, clk2);\n"
      "  specify\n"
      "    $skew(posedge clk1, posedge clk2, 20);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kTimingCheck);
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSkew);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk1");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "clk2");
}

TEST(TimingCheckCommandParsing, SkewLimitIsExpression) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  specparam tSkew = 5;\n"
      "  $skew(posedge clk, data, tSkew);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSkew);
  ASSERT_EQ(tc->limits.size(), 1u);
}

TEST(TimingCheckCommandParsing, SkewRejectsTrailingArgument) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(posedge clk, data, 5, ntfr, extra);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(TimingCheckCommandParsing, SkewWithoutEdgeControls) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(clk1, clk2, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSkew);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kNone);
  EXPECT_EQ(tc->ref_terminal.name, "clk1");
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNone);
  EXPECT_EQ(tc->data_terminal.name, "clk2");
}

TEST(TimingCheckCommandParsing, SkewZeroLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(posedge clk, d, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSkew);
  ASSERT_EQ(tc->limits.size(), 1u);
}

TEST(TimingCheckCommandParsing, SkewMissingLimitIsError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(posedge clk, d);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(TimingCheckCommandParsing, SkewEmptyArgListIsError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew();\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}
