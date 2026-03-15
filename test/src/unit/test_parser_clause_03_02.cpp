// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DesignElements, ModuleDeclKindDistinctValues) {
  EXPECT_NE(ModuleDeclKind::kModule, ModuleDeclKind::kInterface);
  EXPECT_NE(ModuleDeclKind::kModule, ModuleDeclKind::kProgram);
  EXPECT_NE(ModuleDeclKind::kModule, ModuleDeclKind::kChecker);
  EXPECT_NE(ModuleDeclKind::kInterface, ModuleDeclKind::kProgram);
  EXPECT_NE(ModuleDeclKind::kInterface, ModuleDeclKind::kChecker);
  EXPECT_NE(ModuleDeclKind::kProgram, ModuleDeclKind::kChecker);
}

TEST(DesignBuildingBlockParsing, ModuleContainsDeclarationsAndCode) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  wire b;\n"
      "  assign b = a;\n"
      "  always_comb a = 0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->items.empty());
}

TEST(DesignBuildingBlockParsing, ProgramContainsDeclarationsAndCode) {
  auto r = Parse(
      "program p;\n"
      "  logic a;\n"
      "  initial a = 1;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->programs[0]->items.empty());
}

TEST(DesignBuildingBlockParsing, InterfaceContainsDeclarations) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic req, gnt;\n"
      "  logic [7:0] data;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->interfaces[0]->items.empty());
}

TEST(DesignBuildingBlockParsing, CheckerContainsDeclarations) {
  auto r = Parse(
      "checker chk;\n"
      "  logic flag;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->checkers[0]->items.empty());
}

TEST(DesignBuildingBlockParsing, PackageContainsDeclarations) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef int myint;\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->packages[0]->items.empty());
}

TEST(DesignBuildingBlockParsing, TopLevelClassIsNotDesignElement) {
  auto r = Parse(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->programs.empty());
  EXPECT_TRUE(r.cu->interfaces.empty());
  EXPECT_TRUE(r.cu->checkers.empty());
  EXPECT_TRUE(r.cu->packages.empty());
  EXPECT_TRUE(r.cu->udps.empty());
  EXPECT_TRUE(r.cu->configs.empty());
}

TEST(DesignBuildingBlockParsing, CuScopeTypedefIsNotDesignElement) {
  auto r = Parse(
      "typedef int myint;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->packages.empty());
}

TEST(DesignBuildingBlockParsing, CuScopeParamIsNotDesignElement) {
  auto r = Parse(
      "parameter int P = 42;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->packages.empty());
}

TEST(DesignBuildingBlockParsing, UnrecognizedTopLevelTokenIsError) {
  EXPECT_FALSE(ParseOk("always_comb begin end"));
}

TEST(DesignBuildingBlockParsing, BareStatementAtTopLevelIsError) {
  EXPECT_FALSE(ParseOk("assign x = 1;"));
}

TEST(DesignBuildingBlockParsing, AllSevenDesignElementsCoexist) {
  auto r = Parse(
      "module m; endmodule\n"
      "program p; endprogram\n"
      "interface ifc; endinterface\n"
      "checker chk; endchecker\n"
      "package pkg; endpackage\n"
      "primitive udp_id (output out, input in);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n"
      "config cfg; design m; endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->configs.size(), 1u);
}

TEST(DesignBuildingBlockParsing, DesignElementsInterleaveWithNonDesignElements) {
  auto r = Parse(
      "typedef int myint;\n"
      "module m; endmodule\n"
      "class C; int x; endclass\n"
      "package pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->packages.size(), 1u);
}

TEST(DesignBuildingBlockParsing, AllSevenDesignElementsThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m; endmodule\n"
      "program p; endprogram\n"
      "interface ifc; endinterface\n"
      "checker chk; endchecker\n"
      "package pkg; endpackage\n"
      "primitive udp_and (output out, input a, b);\n"
      "  table 0 0 : 0; 0 1 : 0; 1 0 : 0; 1 1 : 1; endtable\n"
      "endprimitive\n"
      "config cfg; design m; endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_EQ(r.cu->modules[0]->decl_kind, ModuleDeclKind::kModule);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "p");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "ifc");
  EXPECT_EQ(r.cu->interfaces[0]->decl_kind, ModuleDeclKind::kInterface);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "chk");
  EXPECT_EQ(r.cu->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "udp_and");
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

// §3.1 — All seven design element types coexist in a single compilation unit.
TEST(CompilationUnitStructure, AllDesignElementTypesCoexist) {
  auto r = Parse(
      "module m; endmodule\n"
      "program p; endprogram\n"
      "interface ifc; endinterface\n"
      "checker chk; endchecker\n"
      "package pkg; endpackage\n"
      "primitive u(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "config cfg;\n"
      "  design m;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->configs.size(), 1u);
}

}  // namespace
