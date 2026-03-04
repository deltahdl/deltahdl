// §31.4.2: $timeskew

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// system_timing_check ::= $timeskew_timing_check
TEST(ParserA705, SystemTimingCheckTimeskew) {
  auto r = Parse("module m;\n"
                 "specify\n"
                 "  $timeskew(posedge clk1, posedge clk2, 5);\n"
                 "endspecify\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kTimeskew);
}

// =============================================================================
// A.7.5.1 $timeskew_timing_check
// =============================================================================
// $timeskew with event_based_flag and remain_active_flag
TEST(ParserA70501, TimeskewWithFlags) {
  auto r = Parse("module m;\n"
                 "specify\n"
                 "  $timeskew(posedge clk1, posedge clk2, 5, ntfr, 1, 0);\n"
                 "endspecify\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kTimeskew);
  EXPECT_EQ(tc->notifier, "ntfr");
  ASSERT_NE(tc->event_based_flag, nullptr);
  ASSERT_NE(tc->remain_active_flag, nullptr);
}

// =============================================================================
// A.7.5.2 event_based_flag / remain_active_flag
// =============================================================================
// $timeskew with event_based_flag and remain_active_flag
TEST(ParserA70502, EventBasedFlagAndRemainActiveFlag) {
  auto r = Parse("module m;\n"
                 "specify\n"
                 "  $timeskew(posedge clk1, posedge clk2, 5, ntfr, 1, 0);\n"
                 "endspecify\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->notifier, "ntfr");
  ASSERT_NE(tc->event_based_flag, nullptr);
  ASSERT_NE(tc->remain_active_flag, nullptr);
}

// remain_active_flag ::= constant_mintypmax_expression
TEST(ParserA70502, RemainActiveFlagMinTypMax) {
  auto r = Parse("module m;\n"
                 "specify\n"
                 "  $timeskew(posedge clk1, posedge clk2, 5, ntfr, 1, 1:2:3);\n"
                 "endspecify\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_NE(tc->remain_active_flag, nullptr);
  EXPECT_EQ(tc->remain_active_flag->kind, ExprKind::kMinTypMax);
}
using ConfigParseTest = ProgramTestParse;

TEST_F(SpecifyTest, TimeskewTimingCheck) {
  auto *cu = Parse("module m;\n"
                   "specify\n"
                   "  $timeskew(posedge clk1, posedge clk2, 5);\n"
                   "endspecify\n"
                   "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto &tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kTimeskew);
  EXPECT_EQ(tc.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.ref_terminal.name, "clk1");
  EXPECT_EQ(tc.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.data_terminal.name, "clk2");
  ASSERT_EQ(tc.limits.size(), 1u);
}

TEST_F(SpecifyTest, TimeskewWithNotifier) {
  auto *cu = Parse("module m;\n"
                   "specify\n"
                   "  $timeskew(posedge clk1, posedge clk2, 5, ntfr);\n"
                   "endspecify\n"
                   "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto &tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kTimeskew);
  EXPECT_EQ(tc.notifier, "ntfr");
}

} // namespace
