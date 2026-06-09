#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TimingCheckCommandParsing, NochangeBasic) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(posedge clk, data, 0, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kNochange);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
  EXPECT_EQ(tc->data_terminal.name, "data");
  ASSERT_EQ(tc->limits.size(), 2u);
}

TEST(TimingCheckCommandParsing, NochangeNegedgeReference) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(negedge clk, data, 0, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kNegedge);
}

TEST(TimingCheckCommandParsing, NochangeStartEndEdgeOffsetMinTypMax) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(posedge clk, data, 1:2:3, 4:5:6);\n"
      "endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_GE(tc->limits.size(), 2u);
  EXPECT_EQ(tc->limits[0]->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(tc->limits[1]->kind, ExprKind::kMinTypMax);
}

TEST(TimingCheckCommandParsing, NochangeWithNotifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(posedge clk, data, 0, 0, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->notifier, "ntfr");
}

TEST(TimingCheckCommandParsing, NochangeEmptyNotifierSlot) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(posedge clk, data, 0, 0, );\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_TRUE(tc->notifier.empty());
}

TEST(TimingCheckCommandParsing, ErrorNochangeEdgeControlSpecifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(edge clk, data, 0, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(TimingCheckCommandParsing, ErrorNochangeMissingEndOffset) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(posedge clk, data, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}
