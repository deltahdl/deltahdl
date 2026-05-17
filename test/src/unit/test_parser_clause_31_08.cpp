#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(VectorSignalsInTimingChecks, SetupVectorDataTerminalParses) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(DAT, posedge CLK, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_terminal.name, "DAT");
}

TEST(VectorSignalsInTimingChecks, SetupBothVectorTerminalsParse) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk[1:0], data[7:0], 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_terminal.range_kind, SpecifyRangeKind::kPartSelect);
  EXPECT_EQ(tc->data_terminal.range_kind, SpecifyRangeKind::kPartSelect);
}

TEST(VectorSignalsInTimingChecks, SetupPlusIndexedDataTerminalParses) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data[0+:8], posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_terminal.range_kind, SpecifyRangeKind::kPlusIndexed);
}

TEST(VectorSignalsInTimingChecks, SetupMinusIndexedDataTerminalParses) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data[7-:8], posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_terminal.range_kind, SpecifyRangeKind::kMinusIndexed);
}

TEST(VectorSignalsInTimingChecks, WidthVectorReferenceTerminalParses) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge rst[3:0], 20);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kWidth);
  EXPECT_EQ(tc->ref_terminal.range_kind, SpecifyRangeKind::kPartSelect);
}

TEST(VectorSignalsInTimingChecks, PeriodVectorReferenceTerminalParses) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(posedge clk[1:0], 100);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kPeriod);
  EXPECT_EQ(tc->ref_terminal.range_kind, SpecifyRangeKind::kPartSelect);
}

TEST(VectorSignalsInTimingChecks, NochangeVectorDataTerminalParses) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(posedge clk, data[7:0], 0, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kNochange);
  EXPECT_EQ(tc->data_terminal.range_kind, SpecifyRangeKind::kPartSelect);
}

}
