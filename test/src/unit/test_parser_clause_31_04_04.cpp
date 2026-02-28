// §31.4.4: $width

#include "fixture_parser.h"

using namespace delta;

namespace {

// system_timing_check ::= $width_timing_check
TEST(ParserA705, SystemTimingCheckWidth) {
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
}

// =============================================================================
// A.7.5.1 $width_timing_check
// =============================================================================
// $width ( controlled_reference_event , timing_check_limit , threshold [ , [
// notifier ] ] )
TEST(ParserA70501, WidthWithThreshold) {
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

}  // namespace
