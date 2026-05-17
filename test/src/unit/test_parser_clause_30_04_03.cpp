#include "fixture_parser.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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
}

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

TEST(SpecifyPathParsing, PathDeclEdgeSensitiveFull) {
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
}

TEST(SpecifyPathParsing, EdgeSensitiveParallelWithoutDataSource) {
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
}

TEST(SpecifyPathParsing, EdgeSensitiveFullEdgeKeywordWithDataSource) {
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

TEST(SpecifyPathParsing, NegedgeFullPath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (negedge clk *> q, qb) = (3, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
}

TEST(SpecifyPathParsing, EdgeKeywordWithPolarityParallel) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (edge clk + => (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kEdge);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kPositive);
  EXPECT_NE(si->path.data_source, nullptr);
}

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

TEST(SpecifyPathParsing, DataSourceWithNegativeOutputPolarity) {
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

TEST(SpecifyPathParsing, DataSourceNoDstPolarity) {
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
  EXPECT_NE(si->path.data_source, nullptr);
  EXPECT_EQ(si->path.dst_polarity, SpecifyPolarity::kNone);
}

TEST(SpecifyPathParsing, PolarityWithEdgeFullPath) {
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

TEST(SpecifyPathParsing, EdgeSensitiveFullWithOutputPolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk *> (q + : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_NE(si->path.data_source, nullptr);
  EXPECT_EQ(si->path.dst_polarity, SpecifyPolarity::kPositive);
}

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

TEST(SpecifyPathParsing, VectorInputWholeVector) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge bus => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
}

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

TEST(SpecifyPathParsing, FullEdgeSensitiveMultipleOutputsWithDataSource) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk *> (q1, q2 : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  ASSERT_GE(si->path.dst_ports.size(), 2u);
  EXPECT_NE(si->path.data_source, nullptr);
}

TEST(SpecifyPathParsing, ErrorDataSourceMissingColon) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => (q d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

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
