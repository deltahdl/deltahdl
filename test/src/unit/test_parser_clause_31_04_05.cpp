// §31.4.5: $period

#include "fixture_parser.h"

using namespace delta;

namespace {

// system_timing_check ::= $period_timing_check
TEST(ParserA705, SystemTimingCheckPeriod) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(posedge clk, 50);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kPeriod);
}

}  // namespace
