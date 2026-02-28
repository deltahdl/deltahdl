// §31.4.2: $timeskew

#include "fixture_parser.h"

using namespace delta;

namespace {

// system_timing_check ::= $timeskew_timing_check
TEST(ParserA705, SystemTimingCheckTimeskew) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $timeskew(posedge clk1, posedge clk2, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kTimeskew);
}

}  // namespace
