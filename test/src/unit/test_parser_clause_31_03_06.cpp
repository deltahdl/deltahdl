// §31.3.6: $recrem

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.1 $recrem_timing_check
// =============================================================================
// $recrem with all 9 arguments
TEST(ParserA70501, RecremFullArgs) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge clk, rst, 8, 3, ntfr, , , dCLK, dRST);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRecrem);
  ASSERT_GE(tc->limits.size(), 2u);
  EXPECT_EQ(tc->notifier, "ntfr");
  EXPECT_EQ(tc->delayed_ref, "dCLK");
  EXPECT_EQ(tc->delayed_data, "dRST");
}

}  // namespace
