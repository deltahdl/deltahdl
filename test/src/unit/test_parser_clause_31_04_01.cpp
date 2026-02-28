// §31.4.1: $skew

#include "fixture_parser.h"

using namespace delta;

namespace {

// system_timing_check ::= $skew_timing_check
TEST(ParserA705, SystemTimingCheckSkew) {
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
}

}  // namespace
