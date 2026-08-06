#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

TEST(TimingCheckCommandParsing, ErrorNochangeEdgeControlSpecifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(edge clk, data, 0, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// End-to-end over the §31.5 edge-control-specifier dependency: an edge[...]
// descriptor list is built from real §31.5 source syntax and driven through the
// parser. Table 31-12 admits only posedge/negedge on the reference, so the
// $nochange edge-control rule rejects this genuine edge-control specifier
// (distinct from the bare-`edge` case above).
TEST(TimingCheckCommandParsing,
     ErrorNochangeEdgeControlSpecifierWithDescriptors) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(edge[01, 10] clk, data, 0, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// Table 31-12 requires the reference_event to be edge triggered. A plain
// terminal with no posedge/negedge keyword is the closest rejected input that
// is distinct from an (also illegal) edge-control specifier.
TEST(TimingCheckCommandParsing, ErrorNochangePlainReferenceNoEdge) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(clk, data, 0, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// The start/end edge offsets are constant expressions (Table 31-12); a named
// specparam is a constant form beyond the literal the LRM example shows, so the
// mintypmax offset positions must accept it.
TEST(TimingCheckCommandParsing, NochangeSpecparamOffsets) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  specparam so = 5, eo = 7;\n"
      "  $nochange(posedge clk, data, so, eo);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->limits.size(), 2u);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kNochange);
}

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
