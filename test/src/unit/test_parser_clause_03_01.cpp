#include "fixture_parser.h"

using namespace delta;

namespace {

// §3.1: Design elements are the primary building blocks. The CompilationUnit
// collects all design element types into separate collections.

TEST(ParserClause03, Cl3_1_EmptySourceProducesValidCU) {
  auto r = Parse("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules.empty());
  EXPECT_TRUE(r.cu->programs.empty());
  EXPECT_TRUE(r.cu->interfaces.empty());
  EXPECT_TRUE(r.cu->checkers.empty());
  EXPECT_TRUE(r.cu->packages.empty());
  EXPECT_TRUE(r.cu->udps.empty());
  EXPECT_TRUE(r.cu->configs.empty());
  EXPECT_TRUE(r.cu->classes.empty());
  EXPECT_TRUE(r.cu->cu_items.empty());
}

TEST(ParserClause03, Cl3_1_ModuleDeclKindDistinctValues) {
  EXPECT_NE(ModuleDeclKind::kModule, ModuleDeclKind::kInterface);
  EXPECT_NE(ModuleDeclKind::kModule, ModuleDeclKind::kProgram);
  EXPECT_NE(ModuleDeclKind::kModule, ModuleDeclKind::kChecker);
  EXPECT_NE(ModuleDeclKind::kInterface, ModuleDeclKind::kProgram);
  EXPECT_NE(ModuleDeclKind::kInterface, ModuleDeclKind::kChecker);
  EXPECT_NE(ModuleDeclKind::kProgram, ModuleDeclKind::kChecker);
}

TEST(ParserClause03, Cl3_1_ModuleIsParsedAsModule) {
  auto r = Parse("module m; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->decl_kind, ModuleDeclKind::kModule);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

TEST(ParserClause03, Cl3_1_ProgramIsParsedAsProgram) {
  auto r = Parse("program p; endprogram");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  EXPECT_EQ(r.cu->programs[0]->name, "p");
}

TEST(ParserClause03, Cl3_1_InterfaceIsParsedAsInterface) {
  auto r = Parse("interface ifc; endinterface");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->decl_kind, ModuleDeclKind::kInterface);
  EXPECT_EQ(r.cu->interfaces[0]->name, "ifc");
}

TEST(ParserClause03, Cl3_1_CheckerIsParsedAsChecker) {
  auto r = Parse("checker chk; endchecker");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
  EXPECT_EQ(r.cu->checkers[0]->name, "chk");
}

TEST(ParserClause03, Cl3_1_PackageIsParsedAsPackage) {
  auto r = Parse("package pkg; endpackage");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

TEST(ParserClause03, Cl3_1_PrimitiveIsParsedAsUdp) {
  auto r = Parse(
      "primitive udp_buf (output out, input in);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "udp_buf");
}

TEST(ParserClause03, Cl3_1_ConfigIsParsedAsConfig) {
  auto r = Parse("module m; endmodule\n"
                  "config cfg; design m; endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

TEST(ParserClause03, Cl3_1_DesignElementsSortedIntoCorrectCollections) {
  auto r = Parse(
      "module m; endmodule\n"
      "program p; endprogram\n"
      "interface ifc; endinterface\n"
      "checker chk; endchecker\n"
      "package pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->packages.size(), 1u);
}

TEST(ParserClause03, Cl3_1_MultipleModulesInOneCU) {
  auto r = Parse("module a; endmodule\nmodule b; endmodule\n"
                  "module c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
  EXPECT_EQ(r.cu->modules[2]->name, "c");
}

TEST(ParserClause03, Cl3_1_DesignElementsAreContainers) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  wire b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.cu->modules[0]->items.empty());
}

TEST(ParserClause03, Cl3_1_MismatchedEndKeywordIsError) {
  EXPECT_FALSE(ParseOk("module m; endprogram"));
}

TEST(ParserClause03, Cl3_1_UnclosedDesignElementIsError) {
  EXPECT_FALSE(ParseOk("module m;"));
}

}  // namespace
