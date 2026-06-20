

#include "fixture_parser.h"

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
  // A name is required: when the keyword is not followed by an identifier,
  // the definition must be diagnosed rather than accepted with an empty name.
  auto r = Parse("module ; endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(ModuleDefinitions, ModuleWithoutEndmoduleIsRejected) {
  // The closing keyword is mandatory: a definition that opens with `module`
  // but is never terminated must be diagnosed rather than silently accepted.
  auto r = Parse("module m;");
  EXPECT_TRUE(r.has_errors);
}

TEST(ModuleDefinitions, MacromoduleWithoutEndmoduleIsRejected) {
  // The same enclosure rule applies when the definition opens with the
  // interchangeable `macromodule` keyword.
  auto r = Parse("macromodule m;");
  EXPECT_TRUE(r.has_errors);
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
