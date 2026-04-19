#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §31.4.6 Syntax 31-14: the five-argument form with reference_event,
// data_event, start_edge_offset, and end_edge_offset parses and is
// classified as a $nochange timing check.
TEST(TimingCheckCommandParsing, NochangeBasic) {
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
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
  EXPECT_EQ(tc->data_terminal.name, "data");
  ASSERT_EQ(tc->limits.size(), 2u);
}

// §31.4.6: "The reference event can be specified with the posedge or
// negedge keyword" — negedge is one of the two allowed keyword forms.
TEST(TimingCheckCommandParsing, NochangeNegedgeReference) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(negedge clk, data, 0, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kNegedge);
}

// §31.4.6 Syntax 31-14: start_edge_offset and end_edge_offset are
// mintypmax expressions; both must reach the AST as distinct limit
// entries.
TEST(TimingCheckCommandParsing, NochangeStartAndEndOffsets) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(posedge clk, data, 3, 7);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->limits.size(), 2u);
  EXPECT_NE(tc->limits[0], nullptr);
  EXPECT_NE(tc->limits[1], nullptr);
}

// §31.4.6: "a negative offset for start edge shrinks the region by
// starting the region later" and "a negative offset for the end edge
// shrinks the region by ending it earlier." Both offset positions must
// therefore accept a unary-minus expression through the mintypmax
// production.
TEST(TimingCheckCommandParsing, NochangeNegativeOffsets) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(posedge clk, data, -3, -5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->limits.size(), 2u);
  EXPECT_NE(tc->limits[0], nullptr);
  EXPECT_NE(tc->limits[1], nullptr);
}

// §31.4.6 Syntax 31-14: start_edge_offset and end_edge_offset are
// mintypmax_expression productions, so a min:typ:max triple must be
// accepted in each offset position.
TEST(TimingCheckCommandParsing, NochangeStartEndEdgeOffsetMinTypMax) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(posedge clk, data, 1:2:3, 4:5:6);\n"
      "endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_GE(tc->limits.size(), 2u);
  EXPECT_EQ(tc->limits[0]->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(tc->limits[1]->kind, ExprKind::kMinTypMax);
}

// §31.4.6 Syntax 31-14: the optional notifier follows the two offsets
// and is captured by the parser as the timing check's notifier name.
TEST(TimingCheckCommandParsing, NochangeWithNotifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(posedge clk, data, 0, 0, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->notifier, "ntfr");
}

// §31.4.6 Syntax 31-14: the trailing `[ , [ notifier ] ]` permits a
// comma with an empty notifier slot — the form must parse with the
// notifier name left unset.
TEST(TimingCheckCommandParsing, NochangeEmptyNotifierSlot) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(posedge clk, data, 0, 0, );\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_TRUE(tc->notifier.empty());
}

// §31.4.6 Table 31-12: reference_event is an "Edge triggered timestamp
// and/or timecheck event" — a bare terminal without posedge/negedge is
// ill-formed.
TEST(TimingCheckCommandParsing, ErrorNochangeReferenceMissingEdge) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(clk, data, 0, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §31.4.6: "the edge-control specifiers (see 31.5) cannot be used."
// The `edge` keyword (with or without a descriptor list) is an
// edge-control specifier and must be rejected on the reference event.
TEST(TimingCheckCommandParsing, ErrorNochangeEdgeControlSpecifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(edge clk, data, 0, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §31.4.6 Syntax 31-14: both start_edge_offset and end_edge_offset are
// mandatory positional arguments — a call with only one offset is
// ill-formed.
TEST(TimingCheckCommandParsing, ErrorNochangeMissingEndOffset) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(posedge clk, data, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
