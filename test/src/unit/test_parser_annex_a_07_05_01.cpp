// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA70501, WidthBasic) {
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
  ASSERT_GE(tc->limits.size(), 2u);
}

TEST(ParserA70501, WidthWithNotifier) {
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
  EXPECT_EQ(tc->notifier, "ntfr");
}

TEST(ParserA70501, NochangeBasic) {
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
}

TEST(ParserA70501, NochangeWithNotifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(posedge clk, data, 0, 0, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kNochange);
  EXPECT_EQ(tc->notifier, "ntfr");
}

TEST(ParserA70501, AllTwelveTimingCheckKinds) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10);\n"
      "  $hold(posedge clk, data, 5);\n"
      "  $setuphold(posedge clk, data, 10, 5);\n"
      "  $recovery(posedge rst, posedge clk, 10);\n"
      "  $removal(posedge rst, posedge clk, 5);\n"
      "  $recrem(posedge rst, posedge clk, 10, 5);\n"
      "  $skew(posedge clk1, posedge clk2, 50);\n"
      "  $timeskew(posedge clk1, posedge clk2, 50);\n"
      "  $fullskew(posedge clk1, posedge clk2, 50, 50);\n"
      "  $period(posedge clk, 50);\n"
      "  $width(posedge clk, 20, 1);\n"
      "  $nochange(posedge clk, data, 0, 0);\n"
      "endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 12u);
  EXPECT_EQ(spec->specify_items[0]->timing_check.check_kind,
            TimingCheckKind::kSetup);
  EXPECT_EQ(spec->specify_items[1]->timing_check.check_kind,
            TimingCheckKind::kHold);
  EXPECT_EQ(spec->specify_items[2]->timing_check.check_kind,
            TimingCheckKind::kSetuphold);
  EXPECT_EQ(spec->specify_items[3]->timing_check.check_kind,
            TimingCheckKind::kRecovery);
  EXPECT_EQ(spec->specify_items[4]->timing_check.check_kind,
            TimingCheckKind::kRemoval);
  EXPECT_EQ(spec->specify_items[5]->timing_check.check_kind,
            TimingCheckKind::kRecrem);
  EXPECT_EQ(spec->specify_items[6]->timing_check.check_kind,
            TimingCheckKind::kSkew);
  EXPECT_EQ(spec->specify_items[7]->timing_check.check_kind,
            TimingCheckKind::kTimeskew);
  EXPECT_EQ(spec->specify_items[8]->timing_check.check_kind,
            TimingCheckKind::kFullskew);
  EXPECT_EQ(spec->specify_items[9]->timing_check.check_kind,
            TimingCheckKind::kPeriod);
  EXPECT_EQ(spec->specify_items[10]->timing_check.check_kind,
            TimingCheckKind::kWidth);
  EXPECT_EQ(spec->specify_items[11]->timing_check.check_kind,
            TimingCheckKind::kNochange);
}

}  // namespace
