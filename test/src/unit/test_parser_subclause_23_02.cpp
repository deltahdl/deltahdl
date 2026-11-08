#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(ModuleDeclarations, MacromoduleKeywordIntroducesModule) {
  auto r = Parse("macromodule mm; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->decl_kind, ModuleDeclKind::kModule);
  EXPECT_EQ(r.cu->modules[0]->name, "mm");
}

TEST(ModuleDeclarations, ModuleNameMatchesIdentifier) {
  auto r = Parse("module my_design; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "my_design");
}

TEST(ModuleDeclarations, ModuleKeywordWithoutNameIsRejected) {
  auto r = Parse("module ; endmodule");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 1, "23.2.1"));
}

TEST(ModuleDeclarations, MacromoduleKeywordWithoutNameIsRejected) {
  auto r = Parse("macromodule ; endmodule");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 1, "23.2.1"));
}

TEST(ModuleDefinitions, ModuleWithoutEndmoduleIsRejected) {
  auto r = Parse("module m;");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endmodule', got EOF", 1, "23.2"));
}

TEST(ModuleDefinitions, MacromoduleWithoutEndmoduleIsRejected) {
  auto r = Parse("macromodule m;");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endmodule', got EOF", 1, "23.2"));
}

TEST(ModuleDefinitions, MultipleModulesInSource) {
  auto r = Parse(
      "module a; endmodule\n"
      "module b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
}

}  // namespace
