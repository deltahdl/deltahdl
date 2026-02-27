// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// Case item with default
TEST(ParserA612, RsCaseItemDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (99)\n"
      "               0: a;\n"
      "               default: b;\n"
      "             endcase;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Default with colon (default :)
TEST(ParserA612, RsCaseItemDefaultColon) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (0)\n"
      "               default : a;\n"
      "             endcase;\n"
      "      a : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — break and return within productions
// =============================================================================
// Break terminates randsequence
TEST(ParserA612, BreakInRandsequence) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a { break; };\n"
      "      a : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Return aborts current production
TEST(ParserA612, ReturnInRandsequence) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a { return; };\n"
      "      a : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — complex / combined constructs
// =============================================================================
// Multiple productions with mixed prods (if, repeat, code_block, items)
TEST(ParserA612, ComplexMixedProds) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : repeat(2) step { $display(\"done\"); };\n"
      "      step : if (1) a else b;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Nested randsequence (randsequence inside code block)
TEST(ParserA612, NestedRandsequence) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(outer)\n"
      "      outer : {\n"
      "        randsequence(inner)\n"
      "          inner : { ; };\n"
      "        endsequence\n"
      "      };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.7 -- Specify section
// =============================================================================
TEST(ParserAnnexA, A7SpecifyParallelPath) {
  auto r = Parse("module m; specify (a => b) = 5; endspecify endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kSpecifyBlock);
  ASSERT_GE(r.cu->modules[0]->items[0]->specify_items.size(), 1u);
}

TEST(ParserAnnexA, A7SpecifyFullPath) {
  auto r =
      Parse("module m; specify (a, b *> c, d) = 10; endspecify endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A7TimingCheckSetup) {
  auto r = Parse(
      "module m;\n"
      "  specify $setup(data, posedge clk, 10); endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A7TimingCheckHold) {
  auto r = Parse(
      "module m;\n"
      "  specify $hold(posedge clk, data, 5); endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A7SpecparamInSpecify) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tRISE = 100;\n"
      "    (a => b) = tRISE;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

ModuleItem* FindSpecifyBlock(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) return item;
  }
  return nullptr;
}

// =============================================================================
// A.7.1 specify_block ::= specify { specify_item } endspecify
// =============================================================================
TEST(ParserA701, SpecifyBlockEmpty) {
  auto r = Parse("module m; specify endspecify endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(spec->kind, ModuleItemKind::kSpecifyBlock);
  EXPECT_EQ(spec->specify_items.size(), 0u);
}

TEST(ParserA701, SpecifyBlockSingleItem) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
}

TEST(ParserA701, SpecifyBlockMultipleItems) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "    (c => d) = 10;\n"
      "    $setup(data, posedge clk, 3);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 3u);
}

// =============================================================================
// A.7.1 specify_item — all 5 alternatives
// =============================================================================
TEST(ParserA701, SpecifyItemSpecparamDecl) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tPD = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kSpecparam);
}

TEST(ParserA701, SpecifyItemPulsestyleDecl) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_onevent out1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPulsestyle);
}

TEST(ParserA701, SpecifyItemShowcancelledDecl) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    showcancelled out1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kShowcancelled);
}

TEST(ParserA701, SpecifyItemPathDecl) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPathDecl);
}

TEST(ParserA701, SpecifyItemSystemTimingCheck) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    $setup(data, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kTimingCheck);
}

TEST(ParserA701, SpecifyItemAllFiveKinds) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tPD = 5;\n"
      "    pulsestyle_onevent out1;\n"
      "    showcancelled out2;\n"
      "    (a => b) = tPD;\n"
      "    $setup(data, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 5u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kSpecparam);
  EXPECT_EQ(spec->specify_items[1]->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_EQ(spec->specify_items[2]->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_EQ(spec->specify_items[3]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[4]->kind, SpecifyItemKind::kTimingCheck);
}

// =============================================================================
// A.7.1 pulsestyle_declaration
// =============================================================================
TEST(ParserA701, PulsestyleOneventSingleOutput) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_onevent out1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_FALSE(item->is_ondetect);
  ASSERT_EQ(item->signal_list.size(), 1u);
  EXPECT_EQ(item->signal_list[0], "out1");
}

TEST(ParserA701, PulsestyleOneventMultipleOutputs) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_onevent out1, out2, out3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_FALSE(item->is_ondetect);
  ASSERT_EQ(item->signal_list.size(), 3u);
  EXPECT_EQ(item->signal_list[0], "out1");
  EXPECT_EQ(item->signal_list[1], "out2");
  EXPECT_EQ(item->signal_list[2], "out3");
}

TEST(ParserA701, PulsestyleOndetectSingleOutput) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_ondetect q;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_TRUE(item->is_ondetect);
  ASSERT_EQ(item->signal_list.size(), 1u);
  EXPECT_EQ(item->signal_list[0], "q");
}

TEST(ParserA701, PulsestyleOndetectMultipleOutputs) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_ondetect q1, q2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto* item = spec->specify_items[0];
  EXPECT_TRUE(item->is_ondetect);
  ASSERT_EQ(item->signal_list.size(), 2u);
  EXPECT_EQ(item->signal_list[0], "q1");
  EXPECT_EQ(item->signal_list[1], "q2");
}

// =============================================================================
// A.7.1 showcancelled_declaration
// =============================================================================
TEST(ParserA701, ShowcancelledSingleOutput) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    showcancelled out1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_FALSE(item->is_noshowcancelled);
  ASSERT_EQ(item->signal_list.size(), 1u);
  EXPECT_EQ(item->signal_list[0], "out1");
}

TEST(ParserA701, ShowcancelledMultipleOutputs) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    showcancelled out1, out2, out3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto* item = spec->specify_items[0];
  EXPECT_FALSE(item->is_noshowcancelled);
  ASSERT_EQ(item->signal_list.size(), 3u);
  EXPECT_EQ(item->signal_list[0], "out1");
  EXPECT_EQ(item->signal_list[1], "out2");
  EXPECT_EQ(item->signal_list[2], "out3");
}

TEST(ParserA701, NoshowcancelledSingleOutput) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    noshowcancelled out1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_TRUE(item->is_noshowcancelled);
  ASSERT_EQ(item->signal_list.size(), 1u);
  EXPECT_EQ(item->signal_list[0], "out1");
}

TEST(ParserA701, NoshowcancelledMultipleOutputs) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    noshowcancelled out1, out2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto* item = spec->specify_items[0];
  EXPECT_TRUE(item->is_noshowcancelled);
  ASSERT_EQ(item->signal_list.size(), 2u);
  EXPECT_EQ(item->signal_list[0], "out1");
  EXPECT_EQ(item->signal_list[1], "out2");
}

// =============================================================================
// A.7.1 specify_block coexistence with other module items
// =============================================================================
TEST(ParserA701, SpecifyBlockCoexistsWithModuleItems) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "  assign a = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kSpecifyBlock);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kContAssign);
}

TEST(ParserA701, MultipleSpecifyBlocksInModule) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "  specify\n"
      "    (c => d) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  int spec_count = 0;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) ++spec_count;
  }
  EXPECT_EQ(spec_count, 2);
}

// =============================================================================
// A.7.1 pulsestyle and showcancelled together
// =============================================================================
TEST(ParserA701, PulsestyleAndShowcancelledTogether) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_ondetect out1;\n"
      "    showcancelled out1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 2u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_TRUE(spec->specify_items[0]->is_ondetect);
  EXPECT_EQ(spec->specify_items[1]->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_FALSE(spec->specify_items[1]->is_noshowcancelled);
}

SpecifyItem* GetSolePathItem(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  if (!spec || spec->specify_items.empty()) return nullptr;
  return spec->specify_items[0];
}

// =============================================================================
// A.7.2 path_declaration — 3 alternatives
// =============================================================================
// path_declaration ::= simple_path_declaration ;
TEST(ParserA702, PathDeclSimpleParallel) {
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
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kNone);
  EXPECT_EQ(si->path.condition, nullptr);
  EXPECT_FALSE(si->path.is_ifnone);
}

// path_declaration ::= simple_path_declaration ; (full connection)
TEST(ParserA702, PathDeclSimpleFull) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a, b *> c) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  ASSERT_EQ(si->path.src_ports.size(), 2u);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
}

// path_declaration ::= edge_sensitive_path_declaration ;
TEST(ParserA702, PathDeclEdgeSensitiveParallel) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
}

// path_declaration ::= edge_sensitive_path_declaration ; (full)
TEST(ParserA702, PathDeclEdgeSensitiveFull) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk *> q, qb) = (3, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  ASSERT_EQ(si->path.dst_ports.size(), 2u);
}

// path_declaration ::= state_dependent_path_declaration ; (if)
TEST(ParserA702, PathDeclStateDependentIf) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (en) (a => b) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.condition, nullptr);
  EXPECT_FALSE(si->path.is_ifnone);
}

// path_declaration ::= state_dependent_path_declaration ; (ifnone)
TEST(ParserA702, PathDeclStateDependentIfnone) {
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
}

// =============================================================================
// A.7.2 simple_path_declaration — parallel_path_description = path_delay_value
// =============================================================================
TEST(ParserA702, SimplePathParallelSingleDelay) {
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
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].name, "b");
  ASSERT_EQ(si->path.delays.size(), 1u);
}

// simple_path_declaration — full_path_description = path_delay_value
TEST(ParserA702, SimplePathFullMultiplePorts) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a, b, c *> x, y) = 12;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  ASSERT_EQ(si->path.src_ports.size(), 3u);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  EXPECT_EQ(si->path.src_ports[1].name, "b");
  EXPECT_EQ(si->path.src_ports[2].name, "c");
  ASSERT_EQ(si->path.dst_ports.size(), 2u);
  EXPECT_EQ(si->path.dst_ports[0].name, "x");
  EXPECT_EQ(si->path.dst_ports[1].name, "y");
}

// =============================================================================
// A.7.2 parallel_path_description — polarity_operator
// =============================================================================
// ( input + => output ) — positive polarity, parallel
TEST(ParserA702, ParallelPathPositivePolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a + => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kPositive);
}

// ( input - => output ) — negative polarity, parallel
TEST(ParserA702, ParallelPathNegativePolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a - => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kNegative);
}

// ( input => output ) — no polarity (default)
TEST(ParserA702, ParallelPathNoPolarity) {
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
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kNone);
}

// =============================================================================
// A.7.2 full_path_description — polarity_operator
// =============================================================================
// ( inputs + *> outputs ) — positive polarity, full
TEST(ParserA702, FullPathPositivePolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a + *> b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kPositive);
}

// ( inputs - *> outputs ) — negative polarity, full
TEST(ParserA702, FullPathNegativePolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a - *> b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kNegative);
}

// ( inputs *> outputs ) — no polarity (default)
TEST(ParserA702, FullPathNoPolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a, b *> c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kNone);
}

// =============================================================================
// A.7.2 edge_identifier — posedge | negedge | edge
// =============================================================================
TEST(ParserA702, EdgeIdentifierPosedge) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
}

TEST(ParserA702, EdgeIdentifierNegedge) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (negedge clk => q) = 8;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kNegedge);
}

TEST(ParserA702, EdgeIdentifierEdge) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (edge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kEdge);
}

// =============================================================================
// A.7.2 edge_sensitive_path_declaration — parallel form
// =============================================================================
// parallel_edge_sensitive_path_description with data_source
TEST(ParserA702, EdgeSensitiveParallelWithDataSource) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].name, "q");
  EXPECT_NE(si->path.data_source, nullptr);
}

// parallel_edge_sensitive_path_description without data_source
TEST(ParserA702, EdgeSensitiveParallelWithoutDataSource) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (negedge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(si->path.data_source, nullptr);
}

// parallel_edge_sensitive_path_description with polarity and data_source
TEST(ParserA702, EdgeSensitiveParallelPolarityAndDataSource) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk + => (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kPositive);
  EXPECT_NE(si->path.data_source, nullptr);
}

// =============================================================================
// A.7.2 edge_sensitive_path_declaration — full form
// =============================================================================
// full_edge_sensitive_path_description with data_source
TEST(ParserA702, EdgeSensitiveFullWithDataSource) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk *> (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_NE(si->path.data_source, nullptr);
}

// full_edge_sensitive_path_description without data_source
TEST(ParserA702, EdgeSensitiveFullWithoutDataSource) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk *> q, qb) = (3, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_EQ(si->path.data_source, nullptr);
}

// full_edge_sensitive_path_description with edge keyword and data_source
TEST(ParserA702, EdgeSensitiveFullEdgeKeywordWithDataSource) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (edge clk *> (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kEdge);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_NE(si->path.data_source, nullptr);
}

// =============================================================================
// A.7.2 state_dependent_path_declaration
// =============================================================================
// if (expr) simple_path_declaration — parallel
TEST(ParserA702, StateDependentIfSimpleParallel) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (en) (a => b) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.condition, nullptr);
  EXPECT_FALSE(si->path.is_ifnone);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
}

}  // namespace
