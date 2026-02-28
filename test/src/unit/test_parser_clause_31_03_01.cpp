// §31.3.1: $setup

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.1 $setup_timing_check
// =============================================================================
// $setup ( data_event , reference_event , timing_check_limit [ , [ notifier ] ]
// )
TEST(ParserA70501, SetupTimingCheck) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(tc->ref_terminal.name, "data");
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->data_terminal.name, "clk");
  ASSERT_EQ(tc->limits.size(), 1u);
}

}  // namespace
