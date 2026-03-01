// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

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

// edge_control_specifier on ref event
TEST(ParserA70503, EdgeControlSpecifierOnRefEvent) {
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

// =============================================================================
// A.7.5.3 specify_terminal_descriptor
// =============================================================================
// specify_terminal_descriptor — simple identifier
TEST(ParserA70503, TerminalSimpleIdentifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_terminal.name, "data");
  EXPECT_EQ(tc->ref_terminal.range_kind, SpecifyRangeKind::kNone);
  EXPECT_EQ(tc->data_terminal.name, "clk");
  EXPECT_EQ(tc->data_terminal.range_kind, SpecifyRangeKind::kNone);
}

// specify_terminal_descriptor with bit select [expr]
TEST(ParserA70503, TerminalBitSelect) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data[0], posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_terminal.name, "data");
  EXPECT_EQ(tc->ref_terminal.range_kind, SpecifyRangeKind::kBitSelect);
  EXPECT_NE(tc->ref_terminal.range_left, nullptr);
}

// specify_terminal_descriptor with part select [expr:expr]
TEST(ParserA70503, TerminalPartSelect) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data[3:0], posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_terminal.name, "data");
  EXPECT_EQ(tc->ref_terminal.range_kind, SpecifyRangeKind::kPartSelect);
  EXPECT_NE(tc->ref_terminal.range_left, nullptr);
  EXPECT_NE(tc->ref_terminal.range_right, nullptr);
}

// specify_terminal_descriptor — interface.port form
TEST(ParserA70503, TerminalInterfaceDotPort) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(intf.data, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_terminal.interface_name, "intf");
  EXPECT_EQ(tc->ref_terminal.name, "data");
}

// specify_terminal_descriptor with bit select on data signal
TEST(ParserA70503, TerminalBitSelectOnDataSignal) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk, data[7], 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_terminal.name, "data");
  EXPECT_EQ(tc->data_terminal.range_kind, SpecifyRangeKind::kBitSelect);
}

// =============================================================================
// A.7.5.3 timing_check_condition / scalar_timing_check_condition
// =============================================================================
// timing_check_condition: bare expression after &&&
TEST(ParserA70503, TimingCheckConditionBare) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& en, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

// timing_check_condition: ( scalar_timing_check_condition )
TEST(ParserA70503, TimingCheckConditionParenthesized) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

}  // namespace
