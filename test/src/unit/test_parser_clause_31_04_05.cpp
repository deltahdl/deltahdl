#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §31.4.5 Syntax 31-13: the controlled_reference_event carries both an
// edge qualifier and a specify terminal — both must land on the AST.
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

// §31.4.5: "Because the data event is not passed as an argument to
// $period, it is derived from the reference event" — Syntax 31-13 has no
// data_event slot, so the AST's data terminal/edge stay empty.
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

// §31.4.5 Syntax 31-13: the optional notifier follows the limit and is
// captured by the parser as the timing check's notifier name.
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

// §31.4.5: "an edge triggered event shall be passed as the reference
// event. A compilation error shall occur if the reference event is not
// an edge specification." A bare terminal without posedge/negedge/edge
// is ill-formed.
TEST(TimingCheckCommandParsing, ErrorPeriodReferenceMissingEdge) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(clk, 50);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §31.4.5 Syntax 31-13: the trailing `[ , [ notifier ] ]` permits a
// comma followed by an empty notifier slot, so a $period call with a
// dangling trailing comma must still parse and leave the notifier name
// unset.
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

// §31.4.5: the reference must be an "edge specification" — `edge` (any
// edge) is one of the legal forms alongside posedge/negedge, so it must
// be accepted without triggering the edge-required compilation error.
TEST(TimingCheckCommandParsing, PeriodAnyEdgeReference) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(edge clk, 50);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kPeriod);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kEdge);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
}

}  // namespace
