#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_specify.h"

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
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kEdge);
  EXPECT_TRUE(tc->ref_edge_descriptors.empty());
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
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kEdge);
  ASSERT_EQ(tc->ref_edge_descriptors.size(), 1u);
  EXPECT_EQ(tc->ref_edge_descriptors[0].first, '0');
  EXPECT_EQ(tc->ref_edge_descriptors[0].second, '1');
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
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kEdge);
  ASSERT_EQ(tc->ref_edge_descriptors.size(), 2u);
  EXPECT_EQ(tc->ref_edge_descriptors[0].first, '0');
  EXPECT_EQ(tc->ref_edge_descriptors[0].second, '1');
  EXPECT_EQ(tc->ref_edge_descriptors[1].first, '1');
  EXPECT_EQ(tc->ref_edge_descriptors[1].second, '0');
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
  ASSERT_EQ(tc->ref_edge_descriptors.size(), 2u);
  EXPECT_EQ(tc->ref_edge_descriptors[0].first, 'x');
  EXPECT_EQ(tc->ref_edge_descriptors[0].second, '0');
  EXPECT_EQ(tc->ref_edge_descriptors[1].first, 'x');
  EXPECT_EQ(tc->ref_edge_descriptors[1].second, '1');
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
  ASSERT_EQ(tc->ref_edge_descriptors.size(), 2u);
  EXPECT_EQ(tc->ref_edge_descriptors[0].first, '0');
  EXPECT_EQ(tc->ref_edge_descriptors[0].second, 'x');
  EXPECT_EQ(tc->ref_edge_descriptors[1].first, '1');
  EXPECT_EQ(tc->ref_edge_descriptors[1].second, 'x');
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
  ASSERT_EQ(tc->ref_edge_descriptors.size(), 2u);
  EXPECT_EQ(tc->ref_edge_descriptors[0].first, '0');
  EXPECT_EQ(tc->ref_edge_descriptors[0].second, 'X');
  EXPECT_EQ(tc->ref_edge_descriptors[1].first, '1');
  EXPECT_EQ(tc->ref_edge_descriptors[1].second, 'Z');
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
  ASSERT_EQ(tc->ref_edge_descriptors.size(), 6u);
}

TEST(EdgeControlSpecifierParsing, SevenDescriptorsError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [01, 0x, 10, 1x, x0, x1, z0] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "edge-control specifier accepts at most six edge_descriptors", 3,
      "31.5"));
}

TEST(EdgeControlSpecifierParsing, EmptyBracketListError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "edge-control specifier requires at least one edge_descriptor",
      3, "31.5"));
}

TEST(EdgeControlSpecifierParsing, MissingCloseBracketError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [01 clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ']', got identifier", 3, "31.5"));
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
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_TRUE(tc->ref_edge_descriptors.empty());
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
  EXPECT_TRUE(ReportedError(r.diags, "invalid edge_descriptor", 3, "31.5"));
}

TEST(EdgeControlSpecifierParsing, ZeroOrOneWithoutZorXIsError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [1, 10] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "invalid edge_descriptor", 3, "31.5"));
}

TEST(EdgeControlSpecifierParsing, DescriptorUppercaseFromXZ) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [X0, Z1] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->ref_edge_descriptors.size(), 2u);
  EXPECT_EQ(tc->ref_edge_descriptors[0].first, 'X');
  EXPECT_EQ(tc->ref_edge_descriptors[0].second, '0');
  EXPECT_EQ(tc->ref_edge_descriptors[1].first, 'Z');
  EXPECT_EQ(tc->ref_edge_descriptors[1].second, '1');
}

TEST(EdgeControlSpecifierParsing, SplitFormLowercaseZ) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [0z, 1z] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->ref_edge_descriptors.size(), 2u);
  EXPECT_EQ(tc->ref_edge_descriptors[0].first, '0');
  EXPECT_EQ(tc->ref_edge_descriptors[0].second, 'z');
  EXPECT_EQ(tc->ref_edge_descriptors[1].first, '1');
  EXPECT_EQ(tc->ref_edge_descriptors[1].second, 'z');
}

TEST(EdgeControlSpecifierParsing, SplitFormEmbeddedSpaceRejected) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, edge [0 x] clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "edge_descriptor may not contain embedded spaces", 3, "31.5"));
}

}  // namespace
