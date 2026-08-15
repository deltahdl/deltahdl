#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(TimingCheckCommandParsing, PeriodEdgeAndTerminal) {
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
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
  ASSERT_GE(tc->limits.size(), 1u);
}

TEST(TimingCheckCommandParsing, PeriodNoDataSignal) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(negedge clk, 50);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kPeriod);
  EXPECT_TRUE(tc->data_terminal.name.empty());
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNone);
}

TEST(TimingCheckCommandParsing, PeriodWithNotifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(posedge clk, 50, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kPeriod);
  EXPECT_EQ(tc->notifier, "ntfr");
}

// Reference-edge input form built from the §31.5 edge-control specifier: an
// edge[...] descriptor is a valid edge specification, so it satisfies $period's
// edge-required reference rule just as posedge/negedge do. The reference
// records the edge kind as kEdge and parses without the missing-edge error.
TEST(TimingCheckCommandParsing, PeriodEdgeControlSpecifierReference) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(edge[01] clk, 50);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kPeriod);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kEdge);
  ASSERT_GE(tc->limits.size(), 1u);
}

TEST(TimingCheckCommandParsing, ErrorPeriodReferenceMissingEdge) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(clk, 50);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "$period reference_event must be an edge specification", 3,
      "31.4.5"));
}

TEST(TimingCheckCommandParsing, PeriodEmptyNotifierSlot) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(posedge clk, 50, );\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kPeriod);
  EXPECT_TRUE(tc->notifier.empty());
}

}  // namespace
