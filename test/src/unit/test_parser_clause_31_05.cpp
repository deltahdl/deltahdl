#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

TEST(EdgeControlSpecifierParsing, SevenDescriptorsError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [01, 0x, 10, 1x, x0, x1, z0] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(EdgeControlSpecifierParsing, EmptyBracketListError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(EdgeControlSpecifierParsing, MissingCloseBracketError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [01 clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

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

TEST(EdgeControlSpecifierParsing, DescriptorDoubleZeroError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [00] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// In the split-token edge_descriptor form (zero_or_one followed by z_or_x), the
// leading digit must be trailed by an x/X/z/Z. A bare 0 or 1 is an incomplete
// edge_descriptor and is rejected. Here the lone 1 has no z_or_x after it, so
// the parser flags it while still recovering to record the following 10.
TEST(EdgeControlSpecifierParsing, ZeroOrOneWithoutZorXIsError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [1, 10] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}
