#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §31.4.2 Syntax 31-10 / Table 31-8: the optional notifier slot is captured
// as a variable identifier alongside the edge-qualified events.
TEST(TimingCheckCommandParsing, TimeskewWithNotifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $timeskew(posedge clk1, posedge clk2, 5, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kTimeskew);
  EXPECT_EQ(tc->notifier, "ntfr");
}

// §31.4.2 Syntax 31-10: the three positional fields — edge-qualified
// reference and data events plus the timing_check_limit — must round-trip
// through the parser without consuming any trailing extension slots.
TEST(TimingCheckCommandParsing, TimeskewAllFields) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $timeskew(posedge clk1, posedge clk2, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kTimeskew);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk1");
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->data_terminal.name, "clk2");
  ASSERT_EQ(tc->limits.size(), 1u);
}

// §31.4.2 Syntax 31-10 / Table 31-8: $timeskew accepts the two trailing
// optional slots event_based_flag and remain_active_flag past the notifier.
TEST(TimingCheckCommandParsing, TimeskewWithFlags) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $timeskew(posedge clk1, posedge clk2, 5, ntfr, 1, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kTimeskew);
  EXPECT_EQ(tc->notifier, "ntfr");
  ASSERT_NE(tc->event_based_flag, nullptr);
  ASSERT_NE(tc->remain_active_flag, nullptr);
}

// §31.4.2 Table 31-8: the limit is a non-negative constant expression, so a
// specparam reference in the limit slot must parse.
TEST(TimingCheckCommandParsing, TimeskewLimitIsExpression) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  specparam tSkew = 5;\n"
      "  $timeskew(posedge clk1, posedge clk2, tSkew);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kTimeskew);
  ASSERT_EQ(tc->limits.size(), 1u);
}

// §31.4.2: the zero limit is the boundary case the LRM calls out for the
// simultaneous-transition carve-out and must parse like any non-negative
// constant.
TEST(TimingCheckCommandParsing, TimeskewZeroLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $timeskew(posedge clk1, posedge clk2, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kTimeskew);
  ASSERT_EQ(tc->limits.size(), 1u);
}

// §31.4.2 Syntax 31-10 makes the timing_check_limit a mandatory positional
// argument — a $timeskew call with only the two events is ill-formed.
TEST(TimingCheckCommandParsing, TimeskewMissingLimitIsError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $timeskew(posedge clk1, posedge clk2);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §31.4.2 Syntax 31-10 requires three positional arguments; an empty
// argument list is ill-formed.
TEST(TimingCheckCommandParsing, TimeskewEmptyArgListIsError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $timeskew();\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §31.4.2 Syntax 31-10: $timeskew is a specify item and must carry the
// kTimingCheck classification alongside its kTimeskew kind.
TEST(TimingCheckCommandParsing, TimeskewAsSpecifyItem) {
  auto sp = ParseSpecifySingle(
      "module m(input clk1, clk2);\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 20);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kTimingCheck);
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kTimeskew);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk1");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "clk2");
}

}  // namespace
