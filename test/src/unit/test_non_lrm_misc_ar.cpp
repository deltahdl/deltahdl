// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

ModuleItem* FindSpecifyBlock(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) return item;
  }
  return nullptr;
}

SpecifyItem* GetSolePathItem(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  if (!spec || spec->specify_items.empty()) return nullptr;
  return spec->specify_items[0];
}

namespace {

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
  VerifyFullPathPorts(si, {"a", "b", "c"}, {"x", "y"});
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
