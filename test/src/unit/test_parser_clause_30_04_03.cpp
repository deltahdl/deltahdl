#include "fixture_parser.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// edge_identifier ::= posedge | negedge | edge -- one observer per alternative.
// The edge keyword is parsed by ParseSpecifyEdge independently of the path
// operator and polarity, so combinations of edge keyword x path_kind x
// polarity are not retested here.
TEST(SpecifyPathParsing, EdgeIdentifierEdge) {
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

// posedge alternative; also the parallel '=>' bare form (second alternative of
// parallel_edge_sensitive_path_description, with no data-source parenthesis).
TEST(SpecifyPathParsing, PosedgeSensitivePath) {
  auto sp = ParseSpecifySingle(
      "module m(input clk, output q);\n"
      "  specify\n"
      "    (posedge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].name, "clk");
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].name, "q");
  EXPECT_EQ(si->path.data_source, nullptr);
}

// negedge alternative.
TEST(SpecifyPathParsing, NegedgeSensitivePath) {
  auto sp = ParseSpecifySingle(
      "module m(input clk, output q);\n"
      "  specify\n"
      "    (negedge clk => q) = 8;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kNegedge);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].name, "clk");
}

// parallel_edge_sensitive_path_description first alternative: '=>' with a
// data-source parenthesis. Also confirms the output descriptor's optional
// polarity_operator is absent (kNone) when not written.
TEST(SpecifyPathParsing, EdgeSensitiveParallelWithDataSource) {
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
  EXPECT_EQ(si->path.dst_polarity, SpecifyPolarity::kNone);
}

// full_edge_sensitive_path_description first alternative: '*>' with a
// data-source parenthesis.
TEST(SpecifyPathParsing, EdgeSensitiveFullWithDataSource) {
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

// full_edge_sensitive_path_description second alternative: '*>' with a bare
// list_of_path_outputs and no data source.
TEST(SpecifyPathParsing, EdgeSensitiveFullWithoutDataSource) {
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
  ASSERT_EQ(si->path.dst_ports.size(), 2u);
}

// Optional polarity_operator after the edge-sensitive input descriptor.
TEST(SpecifyPathParsing, EdgeSensitiveParallelPolarityAndDataSource) {
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

// Optional polarity_operator on the output descriptor, before the colon -- a
// position unique to the edge-sensitive (data-source) path forms.
TEST(SpecifyPathParsing, DataSourceWithOutputPolarity) {
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

// No edge identifier: edge field stays kNone (the parser side of the
// any-transition rule).
TEST(SpecifyPathParsing, NoEdgeIdentifierWithDataSource) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (clk => (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kNone);
  EXPECT_NE(si->path.data_source, nullptr);
}

// A bit-select source records the selected bit (parser-structural facet of the
// vector-source rule; the runtime LSB detection itself is not yet simulated).
TEST(SpecifyPathParsing, VectorInputBitSelectOnLsb) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk[0] => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kBitSelect);
}

// data_source_expression ::= expression -- an arbitrary expression is accepted.
TEST(SpecifyPathParsing, DataSourceCompoundExpression) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => (q : d + e)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.data_source, nullptr);
}

// The data source requires a ':' separator.
TEST(SpecifyPathParsing, ErrorDataSourceMissingColon) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => (q d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// The data source requires an expression after the ':'.
TEST(SpecifyPathParsing, ErrorDataSourceMissingExpression) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => (q :)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}
