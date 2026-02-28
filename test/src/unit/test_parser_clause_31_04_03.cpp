// §31.4.3: $fullskew

#include "fixture_parser.h"

using namespace delta;

namespace {

// system_timing_check ::= $fullskew_timing_check
TEST(ParserA705, SystemTimingCheckFullskew) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $fullskew(posedge clk1, negedge clk2, 4, 6);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kFullskew);
}

}  // namespace
