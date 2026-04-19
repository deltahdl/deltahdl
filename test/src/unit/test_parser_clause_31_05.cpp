#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §31.5 Syntax 31-15: bare `edge` keyword with no descriptor list leaves
// the descriptor vector empty and records the edge kind as `edge`.
TEST(EdgeControlSpecifierParsing, EdgeKeywordNoBrackets) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kEdge);
  EXPECT_TRUE(tc->data_edge_descriptors.empty());
}

// §31.5 Syntax 31-15: a single `01` descriptor parses and is captured on
// the data_event of a $setup check.
TEST(EdgeControlSpecifierParsing, SingleDescriptor01) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [01] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kEdge);
  ASSERT_EQ(tc->data_edge_descriptors.size(), 1u);
  EXPECT_EQ(tc->data_edge_descriptors[0].first, '0');
  EXPECT_EQ(tc->data_edge_descriptors[0].second, '1');
}

// §31.5 Syntax 31-15: `01` and `10` are the two fixed descriptors; both
// appear in a single list.
TEST(EdgeControlSpecifierParsing, Descriptors01And10) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [01, 10] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kEdge);
  ASSERT_EQ(tc->data_edge_descriptors.size(), 2u);
  EXPECT_EQ(tc->data_edge_descriptors[0].first, '0');
  EXPECT_EQ(tc->data_edge_descriptors[0].second, '1');
  EXPECT_EQ(tc->data_edge_descriptors[1].first, '1');
  EXPECT_EQ(tc->data_edge_descriptors[1].second, '0');
}

// §31.5 Syntax 31-15: `z_or_x zero_or_one` form with `x` leads.
TEST(EdgeControlSpecifierParsing, DescriptorsXTransitions) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [x0, x1] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->data_edge_descriptors.size(), 2u);
  EXPECT_EQ(tc->data_edge_descriptors[0].first, 'x');
  EXPECT_EQ(tc->data_edge_descriptors[0].second, '0');
  EXPECT_EQ(tc->data_edge_descriptors[1].first, 'x');
  EXPECT_EQ(tc->data_edge_descriptors[1].second, '1');
}

// §31.5: "Edge transitions involving z are treated the same way as edge
// transitions involving x" — the grammar still accepts `z` as a descriptor
// letter.
TEST(EdgeControlSpecifierParsing, DescriptorsZTransitions) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(edge [z0, z1] clk, data, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->ref_edge_descriptors.size(), 2u);
  EXPECT_EQ(tc->ref_edge_descriptors[0].first, 'z');
  EXPECT_EQ(tc->ref_edge_descriptors[0].second, '0');
  EXPECT_EQ(tc->ref_edge_descriptors[1].first, 'z');
  EXPECT_EQ(tc->ref_edge_descriptors[1].second, '1');
}

// §31.5 Syntax 31-15: `zero_or_one z_or_x` form produces `0x` / `1x`.
TEST(EdgeControlSpecifierParsing, DescriptorsToXTransitions) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [0x, 1x] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->data_edge_descriptors.size(), 2u);
  EXPECT_EQ(tc->data_edge_descriptors[0].first, '0');
  EXPECT_EQ(tc->data_edge_descriptors[0].second, 'x');
  EXPECT_EQ(tc->data_edge_descriptors[1].first, '1');
  EXPECT_EQ(tc->data_edge_descriptors[1].second, 'x');
}

// §31.5 Syntax 31-15: `z_or_x ::= x | X | z | Z` — uppercase X is a valid
// descriptor letter in the `z_or_x zero_or_one` form.
TEST(EdgeControlSpecifierParsing, DescriptorUppercaseXLeading) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [X0, X1] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->data_edge_descriptors.size(), 2u);
  EXPECT_EQ(tc->data_edge_descriptors[0].first, 'X');
  EXPECT_EQ(tc->data_edge_descriptors[0].second, '0');
  EXPECT_EQ(tc->data_edge_descriptors[1].first, 'X');
  EXPECT_EQ(tc->data_edge_descriptors[1].second, '1');
}

// §31.5 Syntax 31-15: uppercase Z is a valid descriptor letter.
TEST(EdgeControlSpecifierParsing, DescriptorUppercaseZLeading) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(edge [Z0, Z1] clk, data, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->ref_edge_descriptors.size(), 2u);
  EXPECT_EQ(tc->ref_edge_descriptors[0].first, 'Z');
  EXPECT_EQ(tc->ref_edge_descriptors[0].second, '0');
  EXPECT_EQ(tc->ref_edge_descriptors[1].first, 'Z');
  EXPECT_EQ(tc->ref_edge_descriptors[1].second, '1');
}

// §31.5 Syntax 31-15: uppercase letters are also accepted in the trailing
// position of the `zero_or_one z_or_x` form.
TEST(EdgeControlSpecifierParsing, DescriptorUppercaseToXZ) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [0X, 1Z] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->data_edge_descriptors.size(), 2u);
  EXPECT_EQ(tc->data_edge_descriptors[0].first, '0');
  EXPECT_EQ(tc->data_edge_descriptors[0].second, 'X');
  EXPECT_EQ(tc->data_edge_descriptors[1].first, '1');
  EXPECT_EQ(tc->data_edge_descriptors[1].second, 'Z');
}

// §31.5: a single list may mix all three alternatives of the
// edge_descriptor production (`01`, `x0`, `z1`).
TEST(EdgeControlSpecifierParsing, DescriptorsMixedForms) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [01, x0, z1] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->data_edge_descriptors.size(), 3u);
  EXPECT_EQ(tc->data_edge_descriptors[0].first, '0');
  EXPECT_EQ(tc->data_edge_descriptors[0].second, '1');
  EXPECT_EQ(tc->data_edge_descriptors[1].first, 'x');
  EXPECT_EQ(tc->data_edge_descriptors[1].second, '0');
  EXPECT_EQ(tc->data_edge_descriptors[2].first, 'z');
  EXPECT_EQ(tc->data_edge_descriptors[2].second, '1');
}

// §31.5: an edge-control specifier can appear on the reference_event
// (here, of a $hold check) as well as the data_event.
TEST(EdgeControlSpecifierParsing, OnReferenceEvent) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(edge [01] clk, data, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kEdge);
  ASSERT_EQ(tc->ref_edge_descriptors.size(), 1u);
  EXPECT_EQ(tc->ref_edge_descriptors[0].first, '0');
  EXPECT_EQ(tc->ref_edge_descriptors[0].second, '1');
}

// §31.5: the list accepts exactly six pairs — the upper bound called out
// by "from one to six pairs of edge transitions".
TEST(EdgeControlSpecifierParsing, SixDescriptorsAccepted) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [01, 0x, 10, 1x, x0, x1] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->data_edge_descriptors.size(), 6u);
}

// §31.5: more than six pairs exceeds the "one to six" bound and is
// rejected.
TEST(EdgeControlSpecifierParsing, SevenDescriptorsError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [01, 0x, 10, 1x, x0, x1, z0] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §31.5 Syntax 31-15: the grammar requires at least one edge_descriptor
// inside the brackets — an empty list is rejected.
TEST(EdgeControlSpecifierParsing, EmptyBracketListError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §31.5 Syntax 31-15: an unclosed descriptor list is a syntax error.
TEST(EdgeControlSpecifierParsing, MissingCloseBracketError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [01 clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §31.5: `posedge clr` is the shorthand the LRM defines for
// `edge[01, 0x, x1] clr`; the parser records the shorthand form as the
// `posedge` edge kind with no descriptor list materialized.
TEST(EdgeControlSpecifierParsing, PosedgeShorthandRecorded) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kPosedge);
  EXPECT_TRUE(tc->data_edge_descriptors.empty());
}

// §31.5: `negedge clr` is the shorthand for `edge[10, x0, 1x] clr`.
TEST(EdgeControlSpecifierParsing, NegedgeShorthandRecorded) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(negedge clk, data, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kNegedge);
  EXPECT_TRUE(tc->ref_edge_descriptors.empty());
}

// §31.5 Syntax 31-15: the `zero_or_one zero_or_one` form covers only the
// literals `01` and `10` — `00` is not produced by any edge_descriptor
// alternative and must be rejected.
TEST(EdgeControlSpecifierParsing, DescriptorDoubleZeroError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [00] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §31.5 Syntax 31-15: `11` is likewise absent from the edge_descriptor
// alternatives and must be rejected.
TEST(EdgeControlSpecifierParsing, DescriptorDoubleOneError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [11] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
