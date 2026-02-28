// §31.3.2: $hold

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.1 $hold_timing_check
// =============================================================================
// $hold ( reference_event , data_event , timing_check_limit [ , [ notifier ] ]
// )
TEST(ParserA70501, HoldTimingCheck) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk, data, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kHold);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
  EXPECT_EQ(tc->data_terminal.name, "data");
}

TEST(ParserAnnexA, A7TimingCheckHold) {
  auto r = Parse(
      "module m;\n"
      "  specify $hold(posedge clk, data, 5); endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
