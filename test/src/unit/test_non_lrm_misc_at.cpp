// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// specify_terminal_descriptor with bit select on data signal
TEST(ParserA70503, TerminalBitSelectOnDataSignal) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk, data[7], 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_terminal.name, "data");
  EXPECT_EQ(tc->data_terminal.range_kind, SpecifyRangeKind::kBitSelect);
}

// =============================================================================
// A.7.5.3 timing_check_condition / scalar_timing_check_condition
// =============================================================================
// timing_check_condition: bare expression after &&&
TEST(ParserA70503, TimingCheckConditionBare) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& en, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

// timing_check_condition: ( scalar_timing_check_condition )
TEST(ParserA70503, TimingCheckConditionParenthesized) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

}  // namespace
