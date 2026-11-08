#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_specify.h"

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
  EXPECT_EQ(si->path.data_source, nullptr);
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
  ASSERT_EQ(si->path.dst_ports.size(), 2u);
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

TEST(SpecifyPathParsing, OutputPolarityMinusSpaced) {
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

TEST(SpecifyPathParsing, OutputPolarityPlusAbutsColon) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clock => (out +: in)) = (10, 8);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->path.dst_polarity, SpecifyPolarity::kPositive);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].name, "out");
  EXPECT_NE(si->path.data_source, nullptr);
}

TEST(SpecifyPathParsing, OutputPolarityMinusAbutsColon) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (negedge clock[0] => (out -: in)) = (10, 8);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(si->path.dst_polarity, SpecifyPolarity::kNegative);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kBitSelect);
  EXPECT_NE(si->path.data_source, nullptr);
}

TEST(SpecifyPathParsing, InputPolarityMinus) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk - => (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kNegative);
  EXPECT_NE(si->path.data_source, nullptr);
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

TEST(SpecifyPathParsing, ErrorDataSourceMissingColon) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => (q d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ':', got identifier", 3, "30.4.3"));
}

TEST(SpecifyPathParsing, ErrorDataSourceMissingExpression) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => (q :)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"));
}

}  // namespace
