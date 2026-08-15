

#include "fixture_parser.h"
#include "helpers_reported_error.h"

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
  // §23.2.1 owns the module header the name belongs to, and the report the
  // missing name draws stands there rather than under §23.2.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 1, "23.2.1"));
}

TEST(ModuleDeclarations, MacromoduleKeywordWithoutNameIsRejected) {
  // The name requirement applies equally on the interchangeable `macromodule`
  // path: with no identifier after the keyword the definition must be
  // diagnosed rather than accepted with an empty name.
  auto r = Parse("macromodule ; endmodule");
  // §23.2.1 owns the module header on the `macromodule` path too.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 1, "23.2.1"));
}

TEST(ModuleDefinitions, ModuleWithoutEndmoduleIsRejected) {
  // The closing keyword is mandatory: a definition that opens with `module`
  // but is never terminated must be diagnosed rather than silently accepted.
  auto r = Parse("module m;");
  // TokenKindName answers "token" for every keyword, so the sentence names
  // neither `endmodule` nor what stood in its place; §23.2 and the line say
  // which report this is.
  EXPECT_TRUE(ReportedError(r.diags, "expected token, got EOF", 1, "23.2"));
}

TEST(ModuleDefinitions, MacromoduleWithoutEndmoduleIsRejected) {
  // The same enclosure rule applies when the definition opens with the
  // interchangeable `macromodule` keyword.
  auto r = Parse("macromodule m;");
  EXPECT_TRUE(ReportedError(r.diags, "expected token, got EOF", 1, "23.2"));
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
