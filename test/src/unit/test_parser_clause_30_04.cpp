#include "fixture_parser.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SpecifyPathParsing, MultiplePathDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "    (c, d *> e) = 10;\n"
      "    (posedge clk => q) = 3;\n"
      "    if (en) (a => b) = 8;\n"
      "    ifnone (a => b) = 15;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 5u);

  for (auto* si : spec->specify_items) {
    EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  }
}

TEST(SpecifyPathParsing, MultiplePathsInSpecifyBlock) {
  auto r = Parse(
      "module m(input a, b, output x, y);\n"
      "  specify\n"
      "    (a => x) = 5;\n"
      "    (b => y) = 7;\n"
      "    (a => y) = 9;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 3u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[1]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[2]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[0]->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(spec->specify_items[1]->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(spec->specify_items[2]->path.path_kind, SpecifyPathKind::kParallel);
}

TEST(SpecifyPathParsing, VectorAndScalarEndpointsAccepted) {
  auto r = Parse(
      "module m(input sel, input [7:0] in1, in2, output [7:0] q);\n"
      "  specify\n"
      "    (in1 => q) = 3;\n"
      "    (sel *> q) = 2;\n"
      "    (sel => sel) = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 3u);
  for (auto* si : spec->specify_items) {
    EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  }
}

}
