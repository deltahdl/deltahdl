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

// =============================================================================
// A.7.5.1 $nochange_timing_check
// =============================================================================
// $nochange with simple integer offsets
TEST(ParserA70501, NochangeTimingCheck) {
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
  ASSERT_GE(tc->limits.size(), 2u);
}

}  // namespace
