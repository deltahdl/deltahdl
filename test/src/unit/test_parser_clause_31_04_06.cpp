// §31.4.6: $nochange

#include "fixture_parser.h"

using namespace delta;

namespace {

// system_timing_check ::= $nochange_timing_check
TEST(ParserA705, SystemTimingCheckNochange) {
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

}  // namespace
