#include "fixture_parser.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Returns the first module-path declaration parsed inside the first specify
// block, or nullptr if there is none. Used to observe that the §A.7.2
// productions are applied by the parser and recorded in the AST.
const SpecifyPathDecl* FirstPathDecl(ModuleItem* block) {
  if (block == nullptr) return nullptr;
  for (auto* it : block->specify_items) {
    if (it->kind == SpecifyItemKind::kPathDecl) return &it->path;
  }
  return nullptr;
}

// --- path_declaration: the terminating ';' and '=' separators, and the
// parenthesization of the path description, are required (negative paths). ---

TEST(SpecifyPathParsing, ErrorPathDeclMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SpecifyPathParsing, ErrorPathDeclMissingEquals) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SpecifyPathParsing, ErrorPathDeclMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SpecifyPathParsing, ErrorPathDeclMissingOpenParen) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// A parallel path ('=>') is described with a single input and a single output
// terminal descriptor (the full '*>' form is the one that takes input/output
// lists). Supplying several terminals on a parallel path is rejected.
TEST(SpecifyPathParsing, ErrorParallelPathMultipleTerminals) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a, b => c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// The single-terminal rule for parallel paths holds for the edge-sensitive
// form too: an edge-sensitive '=>' path with several input terminals (a list,
// which is only valid with '*>') is rejected.
TEST(SpecifyPathParsing, ErrorEdgeSensitiveParallelMultipleTerminals) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge a, b => c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// The 'ifnone' alternative of a state-dependent path declaration accepts only
// a simple path declaration, so an edge-sensitive description after 'ifnone'
// is rejected.
TEST(SpecifyPathParsing, ErrorIfnoneRejectsEdgeSensitivePath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    ifnone (posedge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// --- simple_path_declaration: the parallel ('=>') form followed by
// '= path_delay_value'. The full ('*>') form is exercised by
// FullPathDescriptionInputOutputLists below. ---

TEST_F(SpecifyTest, SimpleParallelPathDeclaration) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(p->edge, SpecifyEdge::kNone);
  EXPECT_EQ(p->condition, nullptr);
  EXPECT_FALSE(p->is_ifnone);
  EXPECT_EQ(p->data_source, nullptr);
  EXPECT_EQ(p->delays.size(), 1u);
}

// --- parallel_path_description: a single input/output terminal pair joined
// by '=>' inside parentheses. ---

TEST_F(SpecifyTest, ParallelPathDescriptionSingleTerminals) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    (in => out) = 3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->path_kind, SpecifyPathKind::kParallel);
  ASSERT_EQ(p->src_ports.size(), 1u);
  ASSERT_EQ(p->dst_ports.size(), 1u);
  EXPECT_EQ(p->src_ports[0].name, "in");
  EXPECT_EQ(p->dst_ports[0].name, "out");
}

// --- full_path_description: lists of inputs/outputs joined by '*>'. ---

TEST_F(SpecifyTest, FullPathDescriptionInputOutputLists) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    (a, b, c *> x, y) = 7;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->path_kind, SpecifyPathKind::kFull);
  EXPECT_EQ(p->src_ports.size(), 3u);
  EXPECT_EQ(p->dst_ports.size(), 2u);
}

// --- Terminal-descriptor input forms consumed by the path descriptions.
// parallel_path_description / full_path_description reference
// specify_input/output_terminal_descriptor (§A.7.3); each descriptor may be a
// plain identifier, a bit-/part-select, or an interface.port reference. Build
// each from real source syntax and confirm the §A.7.2 path production accepts
// and records it. ---

// A parallel path whose input and output terminals are bit-selects.
TEST_F(SpecifyTest, ParallelPathBitSelectTerminals) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    (a[2] => b[2]) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->path_kind, SpecifyPathKind::kParallel);
  ASSERT_EQ(p->src_ports.size(), 1u);
  ASSERT_EQ(p->dst_ports.size(), 1u);
  EXPECT_EQ(p->src_ports[0].name, "a");
  EXPECT_EQ(p->src_ports[0].range_kind, SpecifyRangeKind::kBitSelect);
  EXPECT_EQ(p->dst_ports[0].range_kind, SpecifyRangeKind::kBitSelect);
}

// A full path whose terminals are part-selects.
TEST_F(SpecifyTest, FullPathPartSelectTerminals) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    (a[3:0] *> b[3:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->path_kind, SpecifyPathKind::kFull);
  ASSERT_EQ(p->src_ports.size(), 1u);
  ASSERT_EQ(p->dst_ports.size(), 1u);
  EXPECT_EQ(p->src_ports[0].range_kind, SpecifyRangeKind::kPartSelect);
  EXPECT_EQ(p->dst_ports[0].range_kind, SpecifyRangeKind::kPartSelect);
}

// A path whose terminals are interface.port references (the
// interface_identifier '.' port_identifier form of input/output_identifier).
TEST_F(SpecifyTest, PathInterfacePortTerminals) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    (bus.d => bus.q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->path_kind, SpecifyPathKind::kParallel);
  ASSERT_EQ(p->src_ports.size(), 1u);
  ASSERT_EQ(p->dst_ports.size(), 1u);
  EXPECT_EQ(p->src_ports[0].interface_name, "bus");
  EXPECT_EQ(p->src_ports[0].name, "d");
  EXPECT_EQ(p->dst_ports[0].interface_name, "bus");
  EXPECT_EQ(p->dst_ports[0].name, "q");
}

// --- '= path_delay_value' input forms. A simple_path_declaration binds a
// path_delay_value (§A.7.4), which may be a single expression or a
// parenthesized list of expressions. The single-value form is covered above;
// here the parenthesized multi-value list is built from real syntax and each
// delay expression is recorded. ---

TEST_F(SpecifyTest, SimplePathMultiValueDelay) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (3, 4, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(p->delays.size(), 3u);
}

// --- polarity_operator ::= + | - (optional before '=>'/'*>'). ---

TEST_F(SpecifyTest, PolarityOperatorPositiveParallel) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    (a +=> b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->polarity, SpecifyPolarity::kPositive);
  EXPECT_EQ(p->path_kind, SpecifyPathKind::kParallel);
}

TEST_F(SpecifyTest, PolarityOperatorNegativeFull) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    (a, b -*> c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->polarity, SpecifyPolarity::kNegative);
  EXPECT_EQ(p->path_kind, SpecifyPathKind::kFull);
}

// --- edge_identifier ::= posedge | negedge | edge (leads an edge-sensitive
// path description). ---

TEST_F(SpecifyTest, EdgeIdentifierPosedge) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->edge, SpecifyEdge::kPosedge);
}

TEST_F(SpecifyTest, EdgeIdentifierNegedge) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    (negedge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->edge, SpecifyEdge::kNegedge);
}

TEST_F(SpecifyTest, EdgeIdentifierEdge) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    (edge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->edge, SpecifyEdge::kEdge);
}

// --- parallel_edge_sensitive_path_description: with and without the
// parenthesized '( output [polarity] : data_source_expression )' form. ---

TEST_F(SpecifyTest, ParallelEdgeSensitiveWithDataSource) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => (q : a & b)) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(p->path_kind, SpecifyPathKind::kParallel);
  ASSERT_EQ(p->dst_ports.size(), 1u);
  // data_source_expression ::= expression — a general (binary) expression.
  EXPECT_NE(p->data_source, nullptr);
}

// In the data-source form, the output terminal descriptor may carry its own
// polarity_operator immediately before the ':'.
TEST_F(SpecifyTest, EdgeSensitiveOutputPolarity) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => (q - : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->dst_polarity, SpecifyPolarity::kNegative);
  EXPECT_NE(p->data_source, nullptr);
}

TEST_F(SpecifyTest, ParallelEdgeSensitiveWithoutDataSource) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => q) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(p->path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(p->data_source, nullptr);
}

// --- full_edge_sensitive_path_description: with and without the
// '( outputs [polarity] : data_source_expression )' form. ---

TEST_F(SpecifyTest, FullEdgeSensitiveWithDataSource) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    (negedge clk *> (q1, q2 : d)) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(p->path_kind, SpecifyPathKind::kFull);
  EXPECT_EQ(p->dst_ports.size(), 2u);
  EXPECT_NE(p->data_source, nullptr);
}

TEST_F(SpecifyTest, FullEdgeSensitiveWithoutDataSource) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    (edge clk *> q1, q2) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->edge, SpecifyEdge::kEdge);
  EXPECT_EQ(p->path_kind, SpecifyPathKind::kFull);
  EXPECT_EQ(p->data_source, nullptr);
}

// --- state_dependent_path_declaration: 'if (cond) simple', 'if (cond)
// edge_sensitive', and 'ifnone simple'. ---

TEST_F(SpecifyTest, StateDependentIfSimplePath) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    if (sel) (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_NE(p->condition, nullptr);
  EXPECT_EQ(p->edge, SpecifyEdge::kNone);
  EXPECT_FALSE(p->is_ifnone);
}

TEST_F(SpecifyTest, StateDependentIfEdgeSensitivePath) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    if (sel) (posedge clk => (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_NE(p->condition, nullptr);
  EXPECT_EQ(p->edge, SpecifyEdge::kPosedge);
  EXPECT_NE(p->data_source, nullptr);
}

TEST_F(SpecifyTest, StateDependentIfnoneSimplePath) {
  auto* cu = Parse(
      "module m;\n"
      "  specify\n"
      "    ifnone (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(diag_.HasErrors());
  const auto* p = FirstPathDecl(FirstSpecifyBlock(cu));
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_ifnone);
  EXPECT_EQ(p->condition, nullptr);
}

}  // namespace
