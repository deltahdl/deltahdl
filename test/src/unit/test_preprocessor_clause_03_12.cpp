#include "fixture_parser.h"

using namespace delta;

static const ModuleItem* FindInstByModule(const std::vector<ModuleItem*>& items,
                                          const std::string& module_name) {
  for (const auto* item : items)
    if (item->kind == ModuleItemKind::kModuleInst &&
        item->inst_module == module_name)
      return item;
  return nullptr;
}

namespace {

TEST(DesignBuildingBlockParsing, CompilationAndElaboration) {
  auto r = ParseWithPreprocessor(
      "package pkg; typedef logic [7:0] byte_t; endpackage\n"
      "module adder #(parameter W = 8) (\n"
      "    input [W-1:0] a, b, output [W-1:0] s);\n"
      "  assign s = a + b;\n"
      "endmodule\n"
      "module top; import pkg::*;\n"
      "  wire [15:0] x, y, z;\n"
      "  adder #(16) u0 (.a(x), .b(y), .s(z));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");

  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->params.size(), 1u);

  const auto* inst = FindInstByModule(r.cu->modules[1]->items, "adder");
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_params.size(), 1u);
  EXPECT_EQ(inst->inst_ports.size(), 3u);
}

TEST(DesignBuildingBlockParsing, SyntaxErrorDetectedThroughPipeline) {
  EXPECT_FALSE(ParseWithPreprocessorOk(
      "module m;\n"
      "  assign = ;\n"
      "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, MacroExpansionThenCompilation) {
  auto r = ParseWithPreprocessor(
      "`define WIDTH 16\n"
      "module m #(parameter W = `WIDTH)(\n"
      "    input [W-1:0] a, output [W-1:0] y);\n"
      "  assign y = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params.size(), 1u);
}

TEST(DesignBuildingBlockParsing, AllDesignElementsThroughPipeline) {
  auto r = ParseWithPreprocessor(
      "package pkg; endpackage\n"
      "module m; endmodule\n"
      "program p; endprogram\n"
      "interface ifc; endinterface\n"
      "checker chk; endchecker\n"
      "primitive udp_inv(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
}

}  // namespace
