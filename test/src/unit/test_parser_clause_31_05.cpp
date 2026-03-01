// §31.5: Edge-control specifiers

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.3 edge_control_specifier
// =============================================================================
// edge_control_specifier ::= edge [ edge_descriptor { , edge_descriptor } ]
// edge_descriptor ::= 01 | 10
TEST(ParserA70503, EdgeControlSpecifier01_10) {
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

// Single edge descriptor
TEST(ParserA70503, EdgeControlSpecifierSingle01) {
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

// edge_descriptor ::= z_or_x zero_or_one (x0, x1)
TEST(ParserA70503, EdgeControlSpecifierXTransitions) {
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

// edge_descriptor ::= z_or_x zero_or_one (z0, z1)
TEST(ParserA70503, EdgeControlSpecifierZTransitions) {
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

// edge_descriptor ::= zero_or_one z_or_x (0x, 1x)
TEST(ParserA70503, EdgeControlSpecifierToXTransitions) {
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

// edge without bracket list — no descriptors stored
TEST(ParserA70503, EdgeKeywordWithoutBrackets) {
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

}  // namespace
