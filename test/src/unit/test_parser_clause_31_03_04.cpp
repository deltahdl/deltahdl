// §31.3.4: $removal

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.1 $removal_timing_check
// =============================================================================
TEST(ParserA70501, RemovalTimingCheck) {
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

}  // namespace
