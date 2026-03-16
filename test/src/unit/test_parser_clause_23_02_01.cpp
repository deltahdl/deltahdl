#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(SchedulingSemanticsParsing, StaticModuleLifetime) {
  EXPECT_TRUE(
      ParseOk("module static m;\n"
              "  function int fn();\n"
              "    return 0;\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(ModuleAndHierarchyParsing, EndLabelModule) {
  auto r = Parse("module foo; endmodule : foo\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "foo");
}

TEST(ModuleAndHierarchyParsing, EndLabelModuleNoLabel) {
  auto r = Parse("module bar; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "bar");
}

TEST(ModuleAndHierarchyParsing, ModuleHeaderImport) {
  auto r = Parse(
      "module m import pkg::*; ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");

  ASSERT_GE(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kImportDecl);
}

TEST(ModuleAndHierarchyParsing, ModuleHeaderImportDetails) {
  auto r = Parse(
      "module m import pkg::*; ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->import_item.package_name, "pkg");
  EXPECT_TRUE(mod->items[0]->import_item.is_wildcard);
}

TEST(ModuleAndHierarchyParsing, ModuleHeaderImportWithParamsImport) {
  auto r = Parse(
      "module m import A::*; #(parameter N = 4) (input logic clk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  ASSERT_GE(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kImportDecl);
}

TEST(ModuleAndHierarchyParsing, ModuleHeaderImportWithParamsPortsAndParams) {
  auto r = Parse(
      "module m import A::*; #(parameter N = 4) (input logic clk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->params.size(), 1);
  ASSERT_EQ(mod->ports.size(), 1);
}

TEST(ModuleAndHierarchyParsing, ModuleHeaderMultipleImportsFirst) {
  auto r = Parse(
      "module m import A::*, B::foo; ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  ASSERT_GE(mod->items.size(), 2);
  EXPECT_EQ(mod->items[0]->import_item.package_name, "A");
  EXPECT_TRUE(mod->items[0]->import_item.is_wildcard);
}

TEST(ModuleAndHierarchyParsing, ModuleDefinitionEmpty) {
  auto r = Parse("module empty_mod; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "empty_mod");
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}
TEST(DataTypeParsing, ModuleLifetimeAutomatic) {
  auto r = Parse("module automatic t; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "t");
}

TEST(AttributeParserParsing, TopLevel_TrailingSemicolonAfterEndmodule) {
  EXPECT_TRUE(ParseOk("module m; endmodule;"));
}

TEST(ModuleNoPortList, ModuleNoPortList) {
  auto r = Parse("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
}

}  // namespace
