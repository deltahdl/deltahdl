// Annex A.7.3: Specify block terminals

#include "fixture_parser.h"

using namespace delta;

namespace {

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

}  // namespace
