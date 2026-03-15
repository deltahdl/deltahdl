#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, CompilationProducesAST) {
  auto r = Parse(
      "module m;\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

TEST(DesignBuildingBlockParsing, AllDesignElementTypesCompile) {
  auto r = Parse(
      "module m; endmodule\n"
      "program p; endprogram\n"
      "interface ifc; endinterface\n"
      "checker chk; endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->checkers.size(), 1u);
}

TEST(DesignBuildingBlockParsing, ParameterOverrideCompiles) {
  auto r = Parse(
      "module sub #(parameter W = 8);\n"
      "endmodule\n"
      "module top;\n"
      "  sub #(.W(16)) u0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[1]->items, ModuleItemKind::kModuleInst));
}

TEST(DesignBuildingBlockParsing, PackagePrecedesImport) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "  byte_t data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kImportDecl));
}

TEST(DesignBuildingBlockParsing, OrderOfDesignElements) {
  auto r = Parse(
      "package p; endpackage\n"
      "module a; endmodule\n"
      "module b; a u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
}

TEST(DesignBuildingBlockParsing, SyntaxErrorDetectedDuringCompilation) {
  EXPECT_FALSE(ParseOk("module m;\n"
                        "  assign = ;\n"
                        "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, MissingEndKeywordIsError) {
  EXPECT_FALSE(ParseOk("module m;\n"
                        "  logic x;\n"));
}

TEST(DesignBuildingBlockParsing, PrimitiveDesignElementCompiles) {
  auto r = Parse(
      "primitive udp_or(output y, input a, b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 1;\n"
      "    1 ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "udp_or");
}

TEST(DesignBuildingBlockParsing, AllDesignElementTypesIncludingPackageAndPrimitive) {
  auto r = Parse(
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

TEST(DesignBuildingBlockParsing, InstantiationWithParameterOverrideParsed) {
  auto r = Parse(
      "module sub #(parameter W = 8)(input [W-1:0] a, output [W-1:0] y);\n"
      "  assign y = a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [15:0] x, y;\n"
      "  sub #(16) u0 (.a(x), .y(y));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "W");
  auto* inst = FindItemByKind(r.cu->modules[1]->items,
                              ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "sub");
  EXPECT_EQ(inst->inst_params.size(), 1u);
}

TEST(DesignBuildingBlockParsing, MultiLevelInstantiationCompiles) {
  auto r = Parse(
      "module leaf(input logic a, output logic y);\n"
      "  assign y = ~a;\n"
      "endmodule\n"
      "module mid(input logic a, output logic y);\n"
      "  leaf u0(.a(a), .y(y));\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  mid u0(.a(x), .y(y));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->name, "leaf");
  EXPECT_EQ(r.cu->modules[1]->name, "mid");
  EXPECT_EQ(r.cu->modules[2]->name, "top");
}

TEST(DesignBuildingBlockParsing, DesignElementOrderIndependent) {
  auto r = Parse(
      "module top;\n"
      "  sub u0();\n"
      "endmodule\n"
      "module sub; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
}

}  // namespace
