// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

TimingCheckDecl* GetSoleTimingCheck(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  if (!spec || spec->specify_items.empty()) return nullptr;
  if (spec->specify_items[0]->kind != SpecifyItemKind::kTimingCheck)
    return nullptr;
  return &spec->specify_items[0]->timing_check;
}

namespace {

// ifnone simple_path_declaration
TEST(ParserA702, StateDependentIfnoneSimple) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    ifnone (a => b) = 15;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_TRUE(si->path.is_ifnone);
  EXPECT_EQ(si->path.condition, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
}

// =============================================================================
// A.7.2 polarity_operator — combined forms
// =============================================================================
// Polarity with edge-sensitive full path
TEST(ParserA702, PolarityWithEdgeFullPath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (negedge clk - *> (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kNegative);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_NE(si->path.data_source, nullptr);
}

// Polarity with conditional path
TEST(ParserA702, PolarityWithConditionalPath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (sel) (a + => b) = 8;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.condition, nullptr);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kPositive);
}

// =============================================================================
// A.7.2 data_source_expression with output polarity
// =============================================================================
// Edge-sensitive path with output-side polarity and data source
TEST(ParserA702, DataSourceWithOutputPolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => (q + : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.data_source, nullptr);
  EXPECT_EQ(si->path.dst_polarity, SpecifyPolarity::kPositive);
}

// Edge-sensitive path with negative output polarity and data source
TEST(ParserA702, DataSourceWithNegativeOutputPolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => (q - : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.data_source, nullptr);
  EXPECT_EQ(si->path.dst_polarity, SpecifyPolarity::kNegative);
}

// =============================================================================
// A.7.2 Multiple path declarations in one specify block
// =============================================================================
TEST(ParserA702, MultiplePathDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "    (c, d *> e) = 10;\n"
      "    (posedge clk => q) = 3;\n"
      "    if (en) (a => b) = 8;\n"
      "    ifnone (a => b) = 15;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 5u);
  // All should be path declarations
  for (auto* si : spec->specify_items) {
    EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  }
}

// =============================================================================
// A.7.3 list_of_path_inputs / list_of_path_outputs
// =============================================================================
// list_of_path_inputs — multiple simple input terminals
TEST(ParserA703, ListOfPathInputsMultiple) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a, b, c => d) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 3u);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  EXPECT_EQ(si->path.src_ports[1].name, "b");
  EXPECT_EQ(si->path.src_ports[2].name, "c");
}

// list_of_path_outputs — multiple simple output terminals (full path)
TEST(ParserA703, ListOfPathOutputsMultiple) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a *> x, y, z) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.dst_ports.size(), 3u);
  EXPECT_EQ(si->path.dst_ports[0].name, "x");
  EXPECT_EQ(si->path.dst_ports[1].name, "y");
  EXPECT_EQ(si->path.dst_ports[2].name, "z");
}

// =============================================================================
// A.7.3 specify_input_terminal_descriptor — with constant_range_expression
// =============================================================================
// Input terminal with bit-select
TEST(ParserA703, InputTerminalBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a[3] => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kBitSelect);
  EXPECT_NE(si->path.src_ports[0].range_left, nullptr);
  EXPECT_EQ(si->path.src_ports[0].range_right, nullptr);
}

// Input terminal with part-select range
TEST(ParserA703, InputTerminalPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a[7:0] => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kPartSelect);
  EXPECT_NE(si->path.src_ports[0].range_left, nullptr);
  EXPECT_NE(si->path.src_ports[0].range_right, nullptr);
}

// Input terminal with ascending indexed part-select
TEST(ParserA703, InputTerminalPlusIndexed) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a[0+:4] => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kPlusIndexed);
  EXPECT_NE(si->path.src_ports[0].range_left, nullptr);
  EXPECT_NE(si->path.src_ports[0].range_right, nullptr);
}

// Input terminal with descending indexed part-select
TEST(ParserA703, InputTerminalMinusIndexed) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a[7-:4] => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kMinusIndexed);
  EXPECT_NE(si->path.src_ports[0].range_left, nullptr);
  EXPECT_NE(si->path.src_ports[0].range_right, nullptr);
}

// =============================================================================
// A.7.3 specify_output_terminal_descriptor — with constant_range_expression
// =============================================================================
// Output terminal with bit-select
TEST(ParserA703, OutputTerminalBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b[0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].name, "b");
  EXPECT_EQ(si->path.dst_ports[0].range_kind, SpecifyRangeKind::kBitSelect);
  EXPECT_NE(si->path.dst_ports[0].range_left, nullptr);
}

// Output terminal with part-select range
TEST(ParserA703, OutputTerminalPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b[7:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].name, "b");
  EXPECT_EQ(si->path.dst_ports[0].range_kind, SpecifyRangeKind::kPartSelect);
  EXPECT_NE(si->path.dst_ports[0].range_left, nullptr);
  EXPECT_NE(si->path.dst_ports[0].range_right, nullptr);
}

// Both input and output with range expressions
TEST(ParserA703, BothInputOutputWithRanges) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a[3:0] => b[7:4]) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kPartSelect);
  EXPECT_EQ(si->path.dst_ports[0].name, "b");
  EXPECT_EQ(si->path.dst_ports[0].range_kind, SpecifyRangeKind::kPartSelect);
}

// =============================================================================
// A.7.3 input_identifier / output_identifier — dotted interface.port form
// =============================================================================
// Input identifier — interface_identifier.port_identifier
TEST(ParserA703, InputIdentifierDotted) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (intf.sig => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].interface_name, "intf");
  EXPECT_EQ(si->path.src_ports[0].name, "sig");
}

// Output identifier — interface_identifier.port_identifier
TEST(ParserA703, OutputIdentifierDotted) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => intf.sig) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].interface_name, "intf");
  EXPECT_EQ(si->path.dst_ports[0].name, "sig");
}

// Dotted input with range
TEST(ParserA703, DottedInputWithRange) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (intf.sig[3:0] => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.src_ports[0].interface_name, "intf");
  EXPECT_EQ(si->path.src_ports[0].name, "sig");
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kPartSelect);
}

// Dotted output with range
TEST(ParserA703, DottedOutputWithRange) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => intf.sig[7:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.dst_ports[0].interface_name, "intf");
  EXPECT_EQ(si->path.dst_ports[0].name, "sig");
  EXPECT_EQ(si->path.dst_ports[0].range_kind, SpecifyRangeKind::kPartSelect);
}

// =============================================================================
// A.7.3 Combined forms — terminals with ranges in full/edge/conditional paths
// =============================================================================
// Multiple input terminals with mixed forms in full path
TEST(ParserA703, MixedInputTerminalsFullPath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a, b[3], c[7:0] *> d) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 3u);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kNone);
  EXPECT_EQ(si->path.src_ports[1].name, "b");
  EXPECT_EQ(si->path.src_ports[1].range_kind, SpecifyRangeKind::kBitSelect);
  EXPECT_EQ(si->path.src_ports[2].name, "c");
  EXPECT_EQ(si->path.src_ports[2].range_kind, SpecifyRangeKind::kPartSelect);
}

// Multiple output terminals with mixed forms in full path
TEST(ParserA703, MixedOutputTerminalsFullPath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a *> x[0], y, z[3:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.dst_ports.size(), 3u);
  EXPECT_EQ(si->path.dst_ports[0].name, "x");
  EXPECT_EQ(si->path.dst_ports[0].range_kind, SpecifyRangeKind::kBitSelect);
  EXPECT_EQ(si->path.dst_ports[1].name, "y");
  EXPECT_EQ(si->path.dst_ports[1].range_kind, SpecifyRangeKind::kNone);
  EXPECT_EQ(si->path.dst_ports[2].name, "z");
  EXPECT_EQ(si->path.dst_ports[2].range_kind, SpecifyRangeKind::kPartSelect);
}

// Terminal descriptor with edge-sensitive path
TEST(ParserA703, TerminalWithEdgeSensitivePath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => (q[0] : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].name, "q");
  EXPECT_EQ(si->path.dst_ports[0].range_kind, SpecifyRangeKind::kBitSelect);
  EXPECT_NE(si->path.data_source, nullptr);
}

// Terminal descriptor in state-dependent path
TEST(ParserA703, TerminalInConditionalPath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (en) (a[0] => b[1]) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.condition, nullptr);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kBitSelect);
  EXPECT_EQ(si->path.dst_ports[0].name, "b");
  EXPECT_EQ(si->path.dst_ports[0].range_kind, SpecifyRangeKind::kBitSelect);
}

// All dotted terminals in full path
TEST(ParserA703, AllDottedTerminalsFullPath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (intf1.a, intf2.b *> intf3.c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 2u);
  EXPECT_EQ(si->path.src_ports[0].interface_name, "intf1");
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  EXPECT_EQ(si->path.src_ports[1].interface_name, "intf2");
  EXPECT_EQ(si->path.src_ports[1].name, "b");
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].interface_name, "intf3");
  EXPECT_EQ(si->path.dst_ports[0].name, "c");
}

// Simple terminal — no range, no interface (baseline)
TEST(ParserA703, SimpleTerminalNoRange) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kNone);
  EXPECT_TRUE(si->path.src_ports[0].interface_name.empty());
  EXPECT_EQ(si->path.dst_ports[0].name, "b");
  EXPECT_EQ(si->path.dst_ports[0].range_kind, SpecifyRangeKind::kNone);
  EXPECT_TRUE(si->path.dst_ports[0].interface_name.empty());
}

// =============================================================================
// A.7.4 path_delay_value — bare vs parenthesized
// =============================================================================
// path_delay_value ::= list_of_path_delay_expressions (bare form)
TEST(ParserA704, PathDelayValueBare) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 1u);
}

// path_delay_value ::= ( list_of_path_delay_expressions ) (parenthesized)
TEST(ParserA704, PathDelayValueParenthesized) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 1u);
}

// =============================================================================
// A.7.4 list_of_path_delay_expressions — 1, 2, 3, 6, 12 delays
// =============================================================================
// 1 delay: t_path_delay_expression
TEST(ParserA704, ListOfPathDelayExpr1) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 1u);
}

// 2 delays: trise, tfall
TEST(ParserA704, ListOfPathDelayExpr2) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (3, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 2u);
}

// 3 delays: trise, tfall, tz
TEST(ParserA704, ListOfPathDelayExpr3) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (2, 3, 4);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 3u);
}

// 6 delays: t01, t10, t0z, tz1, t1z, tz0
TEST(ParserA704, ListOfPathDelayExpr6) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = (1, 2, 3, 4, 5, 6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 6u);
}

// 12 delays: t01, t10, t0z, tz1, t1z, tz0, t0x, tx1, t1x, tx0, txz, tzx
TEST(ParserA704, ListOfPathDelayExpr12) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 12u);
}

// =============================================================================
// A.7.4 path_delay_expression ::= constant_mintypmax_expression
// =============================================================================
// Single min:typ:max delay (bare form)
TEST(ParserA704, PathDelayExprMinTypMaxBare) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 1:2:3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 1u);
  EXPECT_EQ(si->path.delays[0]->kind, ExprKind::kMinTypMax);
}

// Single min:typ:max delay (parenthesized)
TEST(ParserA704, PathDelayExprMinTypMaxParenthesized) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1:2:3);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 1u);
  EXPECT_EQ(si->path.delays[0]->kind, ExprKind::kMinTypMax);
}

// 2 delays with min:typ:max (trise, tfall)
TEST(ParserA704, PathDelayExprMinTypMax2) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 2u);
  EXPECT_EQ(si->path.delays[0]->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(si->path.delays[1]->kind, ExprKind::kMinTypMax);
}

// 3 delays with min:typ:max (trise, tfall, tz)
TEST(ParserA704, PathDelayExprMinTypMax3) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1:2:3, 4:5:6, 7:8:9);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 3u);
  for (int i = 0; i < 3; ++i) {
    EXPECT_EQ(si->path.delays[i]->kind, ExprKind::kMinTypMax);
  }
}

// 6 delays with min:typ:max
TEST(ParserA704, PathDelayExprMinTypMax6) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = (1:2:3, 4:5:6, 7:8:9, 10:11:12, 13:14:15, 16:17:18);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 6u);
  for (int i = 0; i < 6; ++i) {
    EXPECT_EQ(si->path.delays[i]->kind, ExprKind::kMinTypMax);
  }
}

// 12 delays with min:typ:max
TEST(ParserA704, PathDelayExprMinTypMax12) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = (1:2:3, 4:5:6, 7:8:9, 10:11:12, 13:14:15, 16:17:18,\n"
      "               19:20:21, 22:23:24, 25:26:27, 28:29:30, 31:32:33, "
      "34:35:36);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 12u);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(si->path.delays[i]->kind, ExprKind::kMinTypMax);
  }
}

// =============================================================================
// A.7.4 path_delay_value with specparam reference
// =============================================================================
// Delay using specparam identifier
TEST(ParserA704, PathDelayWithSpecparam) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tDelay = 10;\n"
      "    (a => b) = tDelay;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_GE(spec->specify_items.size(), 2u);
  auto* path_item = spec->specify_items[1];
  EXPECT_EQ(path_item->kind, SpecifyItemKind::kPathDecl);
  ASSERT_EQ(path_item->path.delays.size(), 1u);
}

// Rise/fall delays using specparam identifiers
TEST(ParserA704, PathDelayRiseFallSpecparams) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tRise = 3;\n"
      "    specparam tFall = 5;\n"
      "    (a => b) = (tRise, tFall);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.7.4 Invalid delay counts (not 1, 2, 3, 6, or 12)
// =============================================================================
// 4 delays — invalid
TEST(ParserA704, InvalidDelayCount4) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1, 2, 3, 4);\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// 5 delays — invalid
TEST(ParserA704, InvalidDelayCount5) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1, 2, 3, 4, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// =============================================================================
// A.7.4 6 and 12 delays on parallel and full paths
// =============================================================================
// 6 delays on a parallel path
TEST(ParserA704, SixDelaysParallelPath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1, 2, 3, 4, 5, 6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  ASSERT_EQ(si->path.delays.size(), 6u);
}

// 12 delays on a parallel path
TEST(ParserA704, TwelveDelaysParallelPath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  ASSERT_EQ(si->path.delays.size(), 12u);
}

// 6 delays with edge-sensitive path
TEST(ParserA704, SixDelaysEdgeSensitive) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => q) = (1, 2, 3, 4, 5, 6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  ASSERT_EQ(si->path.delays.size(), 6u);
}

// 6 delays with conditional path
TEST(ParserA704, SixDelaysConditionalPath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (en) (a => b) = (1, 2, 3, 4, 5, 6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.condition, nullptr);
  ASSERT_EQ(si->path.delays.size(), 6u);
}

// =============================================================================
// A.7.5 system_timing_check — dispatch to 12 timing check types
// =============================================================================
// system_timing_check ::= $setup_timing_check
TEST(ParserA705, SystemTimingCheckSetup) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSetup);
}

// system_timing_check ::= $hold_timing_check
TEST(ParserA705, SystemTimingCheckHold) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk, data, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kHold);
}

// system_timing_check ::= $setuphold_timing_check
TEST(ParserA705, SystemTimingCheckSetuphold) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSetuphold);
}

// system_timing_check ::= $recovery_timing_check
TEST(ParserA705, SystemTimingCheckRecovery) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recovery(posedge clk, rst, 8);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRecovery);
}

// system_timing_check ::= $removal_timing_check
TEST(ParserA705, SystemTimingCheckRemoval) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $removal(posedge clk, rst, 3);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRemoval);
}

// system_timing_check ::= $recrem_timing_check
TEST(ParserA705, SystemTimingCheckRecrem) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge clk, rst, 8, 3);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRecrem);
}

}  // namespace
