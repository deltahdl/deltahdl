

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DesignElementParsing, ModuleKeywordIntroducesModuleDesignElement) {
  auto r = Parse("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_EQ(r.cu->modules[0]->decl_kind, ModuleDeclKind::kModule);
}

TEST(DesignElementParsing, ProgramKeywordIntroducesProgramDesignElement) {
  auto r = Parse("program p; endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "p");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

TEST(DesignElementParsing, InterfaceKeywordIntroducesInterfaceDesignElement) {
  auto r = Parse("interface i; endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "i");
  EXPECT_EQ(r.cu->interfaces[0]->decl_kind, ModuleDeclKind::kInterface);
}

TEST(DesignElementParsing, CheckerKeywordIntroducesCheckerDesignElement) {
  auto r = Parse("checker c; endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "c");
  EXPECT_EQ(r.cu->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
}

TEST(DesignElementParsing, PackageKeywordIntroducesPackageDesignElement) {
  auto r = Parse("package pk; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pk");
}

TEST(DesignElementParsing, PrimitiveKeywordIntroducesPrimitiveDesignElement) {
  auto r = Parse(
      "primitive pr(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "pr");
}

TEST(DesignElementParsing, ConfigKeywordIntroducesConfigurationDesignElement) {
  auto r = Parse(
      "module m; endmodule\n"
      "config cfg;\n"
      "  design m;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

TEST(DesignElementParsing, AllSevenDesignElementsCoexistInOneCompilationUnit) {
  auto r = Parse(
      "module m; endmodule\n"
      "program p; endprogram\n"
      "interface i; endinterface\n"
      "checker c; endchecker\n"
      "package pk; endpackage\n"
      "primitive pr(output y, input a);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
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

}  // namespace
