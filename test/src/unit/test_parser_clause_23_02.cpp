// §23.2

#include "fixture_parser.h"

using namespace delta;

namespace {

// §3.1 — End labels on design elements parse correctly.
TEST(ModuleEndLabel, EndLabelMatchesModuleName) {
  auto r = Parse("module foo; endmodule : foo\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "foo");
}

// §3.1 — Error: missing end-keyword.
TEST(ModuleDefinitions, MissingEndmoduleIsError) {
  EXPECT_FALSE(ParseOk("module m;"));
}

TEST(ModuleDeclarations, ModuleKeywordIntroducesModule) {
  auto r = Parse("module m; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->decl_kind, ModuleDeclKind::kModule);
}

TEST(ModuleDeclarations, MacromoduleKeywordIntroducesModule) {
  auto r = Parse("macromodule mm; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->decl_kind, ModuleDeclKind::kModule);
  EXPECT_EQ(r.cu->modules[0]->name, "mm");
}

TEST(ModuleDeclarations, ModuleContainsDeclarationsAndCode) {
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

TEST(ModuleDefinition, Mux2to1WithAnsiPorts) {
  auto r = Parse(
      "module mux2to1 (input wire a, b, sel,\n"
      "                output logic y);\n"
      "  always_comb begin\n"
      "    if (sel) y = a;\n"
      "    else     y = b;\n"
      "  end\n"
      "endmodule: mux2to1\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "mux2to1");
  EXPECT_FALSE(r.cu->modules[0]->ports.empty());
  EXPECT_FALSE(r.cu->modules[0]->items.empty());
}

}  // namespace
