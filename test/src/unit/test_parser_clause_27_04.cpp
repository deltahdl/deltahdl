#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(LoopGenerateParsing, GenvarDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(mod->items[0]->name, "i");
}

TEST(LoopGenerateParsing, GenvarMultipleDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  genvar i, j, k;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 3);
  EXPECT_EQ(mod->items[0]->name, "i");
  EXPECT_EQ(mod->items[1]->name, "j");
  EXPECT_EQ(mod->items[2]->name, "k");
}

TEST(LoopGenerateParsing, ParameterizedModuleWithGenerate) {
  auto r = Parse(
      "module gray2bin #(parameter SIZE = 8) (\n"
      "  output [SIZE-1:0] bin,\n"
      "  input [SIZE-1:0] gray);\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < SIZE; i = i + 1) begin : bitnum\n"
      "      assign bin[i] = ^gray[SIZE-1:i];\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "gray2bin");
  ASSERT_EQ(mod->params.size(), 1);
  EXPECT_EQ(mod->params[0].first, "SIZE");
  ASSERT_EQ(mod->ports.size(), 2);
}

// §27.4 permits genvar declarations to appear either at module scope or
// inside a generate region, so the parser should accept both placements.
TEST(LoopGenerateParsing, GenvarDeclaredInsideGenerateRegion) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  generate\n"
      "    genvar i;\n"
      "    for (i = 0; i < 2; i = i + 1) begin\n"
      "      wire w;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n"));
}

}  // namespace
