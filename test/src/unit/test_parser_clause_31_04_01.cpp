#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §31.4.1 Syntax 31-9: bare three-argument form accepting an edge-qualified
// reference_event and an edge-qualified data_event with a timing_check_limit.
TEST(TimingCheckCommandParsing, SkewBasic) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(posedge clk1, negedge clk2, 3);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSkew);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk1");
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(tc->data_terminal.name, "clk2");
  ASSERT_EQ(tc->limits.size(), 1u);
  EXPECT_TRUE(tc->notifier.empty());
}

// §31.4.1 Syntax 31-9 / Table 31-7: the optional notifier is captured as a
// variable identifier alongside the edge and terminal of each event.
TEST(TimingCheckCommandParsing, SkewWithNotifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(posedge clk1, negedge clk2, 3, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSkew);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk1");
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(tc->data_terminal.name, "clk2");
  EXPECT_EQ(tc->notifier, "ntfr");
}

// §31.4.1 Syntax 31-9: $skew is a specify item and must carry the
// kTimingCheck classification alongside its kSkew kind.
TEST(TimingCheckCommandParsing, SkewAsSpecifyItem) {
  auto sp = ParseSpecifySingle(
      "module m(input clk1, clk2);\n"
      "  specify\n"
      "    $skew(posedge clk1, posedge clk2, 20);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kTimingCheck);
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSkew);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk1");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "clk2");
}

// §31.4.1 Table 31-7: the limit is a non-negative constant expression, so a
// specparam reference in the limit position must parse.
TEST(TimingCheckCommandParsing, SkewLimitIsExpression) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  specparam tSkew = 5;\n"
      "  $skew(posedge clk, data, tSkew);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSkew);
  ASSERT_EQ(tc->limits.size(), 1u);
}

// §31.4.1 Syntax 31-9 defines no trailing arguments past the notifier —
// unlike $timeskew/$fullskew (event_based_flag/remain_active_flag) or
// $setuphold/$recrem (timestamp/timecheck conditions, delayed terminals),
// $skew accepts only the four positional slots.
TEST(TimingCheckCommandParsing, SkewRejectsTrailingArgument) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(posedge clk, data, 5, ntfr, extra);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §31.4.1 Syntax 31-9: reference_event and data_event are both
// timing_check_event productions whose event control prefix is optional, so
// bare terminals without an edge qualifier must still parse.
TEST(TimingCheckCommandParsing, SkewWithoutEdgeControls) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(clk1, clk2, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSkew);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kNone);
  EXPECT_EQ(tc->ref_terminal.name, "clk1");
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNone);
  EXPECT_EQ(tc->data_terminal.name, "clk2");
}

// §31.4.1 Table 31-7 allows a non-negative limit, so the boundary value
// zero must parse — and is independently called out in the LRM as the
// condition under which simultaneous transitions still do not violate.
TEST(TimingCheckCommandParsing, SkewZeroLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(posedge clk, d, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSkew);
  ASSERT_EQ(tc->limits.size(), 1u);
}

// §31.4.1 Syntax 31-9 makes the timing_check_limit a mandatory positional
// argument — a $skew call with only the two events is ill-formed.
TEST(TimingCheckCommandParsing, SkewMissingLimitIsError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(posedge clk, d);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §31.4.1 Syntax 31-9 requires all three positional arguments; an empty
// argument list is ill-formed.
TEST(TimingCheckCommandParsing, SkewEmptyArgListIsError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew();\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
