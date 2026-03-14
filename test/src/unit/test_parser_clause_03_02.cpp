#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, ModuleDeclKindDistinctValues) {
  EXPECT_NE(ModuleDeclKind::kModule, ModuleDeclKind::kInterface);
  EXPECT_NE(ModuleDeclKind::kModule, ModuleDeclKind::kProgram);
  EXPECT_NE(ModuleDeclKind::kModule, ModuleDeclKind::kChecker);
  EXPECT_NE(ModuleDeclKind::kInterface, ModuleDeclKind::kProgram);
  EXPECT_NE(ModuleDeclKind::kInterface, ModuleDeclKind::kChecker);
  EXPECT_NE(ModuleDeclKind::kProgram, ModuleDeclKind::kChecker);
}

TEST(DesignBuildingBlockParsing, ModuleKeywordIntroducesModule) {
  auto r = Parse("module m; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->decl_kind, ModuleDeclKind::kModule);
}

TEST(DesignBuildingBlockParsing, MacromoduleKeywordIntroducesModule) {
  auto r = Parse("macromodule mm; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->decl_kind, ModuleDeclKind::kModule);
  EXPECT_EQ(r.cu->modules[0]->name, "mm");
}

TEST(DesignBuildingBlockParsing, ProgramKeywordIntroducesProgram) {
  auto r = Parse("program p; endprogram");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

TEST(DesignBuildingBlockParsing, InterfaceKeywordIntroducesInterface) {
  auto r = Parse("interface ifc; endinterface");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->decl_kind, ModuleDeclKind::kInterface);
}

TEST(DesignBuildingBlockParsing, CheckerKeywordIntroducesChecker) {
  auto r = Parse("checker chk; endchecker");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
}

TEST(DesignBuildingBlockParsing, PackageKeywordIntroducesPackage) {
  auto r = Parse("package pkg; endpackage");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

TEST(DesignBuildingBlockParsing, PrimitiveKeywordIntroducesPrimitive) {
  auto r = Parse(
      "primitive udp_buf (output out, input in);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "udp_buf");
}

TEST(DesignBuildingBlockParsing, ConfigKeywordIntroducesConfig) {
  auto r = Parse(
      "module m; endmodule\n"
      "config cfg; design m; endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
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

}  // namespace
