#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DeclarationListParsing, ListOfGenvarIdentifiersMultiple) {
  auto r = Parse("module m; genvar i, j, k; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "i");
  EXPECT_EQ(r.cu->modules[0]->items[1]->name, "j");
  EXPECT_EQ(r.cu->modules[0]->items[2]->name, "k");
}

TEST(GenerateRegion, DirectRegionNestingRejected) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    generate\n"
      "    endgenerate\n"
      "  endgenerate\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GenerateRegion, RegionNestedInGenerateIfBodyRejected) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    if (1) begin\n"
      "      generate\n"
      "      endgenerate\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GenerateRegion, RegionNestedInGenerateForBodyRejected) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < 2; i = i + 1) begin\n"
      "      generate\n"
      "      endgenerate\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GenerateRegion, GenerateRegionAtModuleScopeAllowedOncePerSibling) {
  // Sibling (non-nested) regions are fine.
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  generate\n"
      "    wire a;\n"
      "  endgenerate\n"
      "  generate\n"
      "    wire b;\n"
      "  endgenerate\n"
      "endmodule\n"));
}

TEST(GenerateRegion, MissingEndgenerateRejected) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    wire w;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GenerateRegion, OptionalRegionKeywordsProduceSameItems) {
  // §27.3: generate/endgenerate keywords have no semantic significance.
  // Items accepted directly at module scope are equivalent to items wrapped
  // in a generate region.
  auto with_region = Parse(
      "module m;\n"
      "  generate\n"
      "    if (1) begin : blk\n"
      "      wire w;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  auto without_region = Parse(
      "module m;\n"
      "  if (1) begin : blk\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(with_region.cu, nullptr);
  ASSERT_NE(without_region.cu, nullptr);
  EXPECT_FALSE(with_region.has_errors);
  EXPECT_FALSE(without_region.has_errors);
  ASSERT_EQ(with_region.cu->modules[0]->items.size(),
            without_region.cu->modules[0]->items.size());
  EXPECT_EQ(with_region.cu->modules[0]->items[0]->kind,
            without_region.cu->modules[0]->items[0]->kind);
}

TEST(GenerateRegion, EmptyRegionProducesNoItems) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

}  // namespace
