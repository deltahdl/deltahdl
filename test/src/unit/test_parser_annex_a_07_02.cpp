#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "fixture_specify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"

using namespace delta;

namespace {

const SpecifyPathDecl* FirstPathDecl(ModuleItem* block) {
  if (block == nullptr) return nullptr;
  for (auto* it : block->specify_items) {
    if (it->kind == SpecifyItemKind::kPathDecl) return &it->path;
  }
  return nullptr;
}

TEST(SpecifyPathParsing, ErrorPathDeclMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endspecify'", 4, "30.4"));
}

TEST(SpecifyPathParsing, ErrorPathDeclMissingEquals) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '=', got integer literal", 3, "30.5"));
}

TEST(SpecifyPathParsing, ErrorPathDeclMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got '='", 3, "30.4"));
}

TEST(SpecifyPathParsing, ErrorPathDeclMissingOpenParen) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "unexpected token in specify block", 3, "30.3"));
}

TEST(SpecifyPathParsing, ErrorParallelPathMultipleTerminals) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a, b => c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "parallel path '=>' requires a single source and "
                            "destination terminal",
                            3, "30.4.5"));
}

TEST(SpecifyPathParsing, ErrorEdgeSensitiveParallelMultipleTerminals) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (posedge a, b => c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "parallel path '=>' requires a single source and "
                            "destination terminal",
                            3, "30.4.5"));
}

TEST(SpecifyPathParsing, ErrorIfnoneRejectsEdgeSensitivePath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    ifnone (posedge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "ifnone requires a simple path declaration", 3, "30.4.4.4"));
}

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
  EXPECT_NE(p->data_source, nullptr);
}

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

TEST(SpecifyPathParsing, ErrorPathEqualsIsNoPathOperator) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a = b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "path joins its source to its destination with '=>' or '*>'", 3,
      "30.4.2"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(SpecifyPathParsing, ErrorPathArrowIsNoPathOperator) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a -> b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "path joins its source to its destination with '=>' or '*>'", 3,
      "30.4.2"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(SpecifyPathParsing, ErrorPolarityWithoutPathOperatorIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a +> b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "path joins its source to its destination with '=>' or '*>'", 3,
      "30.4.2"));
}

TEST(SpecifyPathParsing, ErrorPathWithoutOperatorIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "path joins its source to its destination with '=>' or '*>'", 3,
      "30.4.2"));
  EXPECT_EQ(r.diags.size(), 1u);
}

}  // namespace
