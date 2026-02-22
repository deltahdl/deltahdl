// Tests for A.7.3 — Specify block terminals

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

ModuleItem *FindSpecifyBlock(const std::vector<ModuleItem *> &items) {
  for (auto *item : items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) return item;
  }
  return nullptr;
}

SpecifyItem *GetSolePathItem(ParseResult &r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  if (!spec || spec->specify_items.empty()) return nullptr;
  return spec->specify_items[0];
}

}  // namespace

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
  auto *si = GetSolePathItem(r);
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
  auto *si = GetSolePathItem(r);
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
  auto *si = GetSolePathItem(r);
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
  auto *si = GetSolePathItem(r);
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
  auto *si = GetSolePathItem(r);
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
  auto *si = GetSolePathItem(r);
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
  auto *si = GetSolePathItem(r);
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
  auto *si = GetSolePathItem(r);
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
  auto *si = GetSolePathItem(r);
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
  auto *si = GetSolePathItem(r);
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
  auto *si = GetSolePathItem(r);
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
  auto *si = GetSolePathItem(r);
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
  auto *si = GetSolePathItem(r);
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
  auto *si = GetSolePathItem(r);
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
  auto *si = GetSolePathItem(r);
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
  auto *si = GetSolePathItem(r);
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
  auto *si = GetSolePathItem(r);
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
  auto *si = GetSolePathItem(r);
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
  auto *si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kNone);
  EXPECT_TRUE(si->path.src_ports[0].interface_name.empty());
  EXPECT_EQ(si->path.dst_ports[0].name, "b");
  EXPECT_EQ(si->path.dst_ports[0].range_kind, SpecifyRangeKind::kNone);
  EXPECT_TRUE(si->path.dst_ports[0].interface_name.empty());
}
