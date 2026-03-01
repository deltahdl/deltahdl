// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// timing_check_condition: ( scalar_timing_check_condition )
TEST(ParserA70503, TimingCheckConditionParenthesized) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

}  // namespace
