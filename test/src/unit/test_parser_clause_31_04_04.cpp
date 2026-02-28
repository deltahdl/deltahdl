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

}  // namespace
