#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_specify.h"

using namespace delta;
namespace {

TEST(ModulePathDeclParsing, PathInsideSpecifyPairsSourceAndDestination) {
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
  auto* si = spec->specify_items[0];
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  EXPECT_EQ(si->path.dst_ports[0].name, "b");
}

TEST(ModulePathDeclParsing, PathOutsideSpecifyBlockRejected) {
  auto r = Parse(
      "module m;\n"
      "  (a => b) = 5;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "unexpected token in module body", 2, "23.2.4"));
}

TEST(ModulePathDeclParsing, SimpleEdgeAndStateDependentPathsRecognized) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "    (posedge clk => q) = 5;\n"
      "    if (en) (c => d) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 3u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[0]->path.edge, SpecifyEdge::kNone);
  EXPECT_EQ(spec->specify_items[0]->path.condition, nullptr);
  EXPECT_EQ(spec->specify_items[1]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[1]->path.edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(spec->specify_items[2]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_NE(spec->specify_items[2]->path.condition, nullptr);
}

}  // namespace
