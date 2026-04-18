#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

TEST(ModuleAndHierarchyParsing, ModuleHeaderImportFollowedByParamAndPort) {
  auto r = Parse(
      "module m import A::*; #(parameter N = 4) (input logic clk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->params.size(), 1);
  ASSERT_EQ(mod->ports.size(), 1);
}

TEST(ModuleAndHierarchyParsing, ModuleHeaderMultipleImports) {
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

TEST(ModuleHeaderDefinition, ImportInHeaderFollowedByPorts) {
  auto r = Parse(
      "module m import pkg::*; (input a, output b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

TEST(ModuleHeaderDefinition, ImportInHeaderFollowedByParams) {
  auto r = Parse(
      "module m import pkg::*; #(parameter int W = 8) (input a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleHeaderDefinition, ImportInHeaderFollowedByBoth) {
  auto r = Parse(
      "module m import pkg::*; #(parameter int W = 8) (input a, output b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleHeaderDefinition, NonAnsiHeaderWithImport) {
  auto r = Parse(
      "module m import pkg::*; (a);\n"
      "  input a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ProgramDeclaration, AnsiHeaderWithPackageImportAndPortList) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef int word_t;\n"
      "endpackage\n"
      "program prg import pkg::*; (input logic clk);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->ports.size(), 1u);
}

TEST(ProgramDeclaration, AnsiHeaderPackageImportRequiresPortList) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "program prg import pkg::*;\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(InterfaceParsing, PackageImportInNonAnsiHeader) {
  EXPECT_TRUE(
      ParseOk("package pkg; typedef int t; endpackage\n"
              "interface ifc import pkg::*; (clk);\n"
              "  input clk;\n"
              "endinterface\n"));
}

TEST(InterfaceParsing, PackageImportInAnsiHeaderWithPortDecls) {
  EXPECT_TRUE(
      ParseOk("package pkg; typedef int t; endpackage\n"
              "interface ifc import pkg::*; (input logic clk);\n"
              "endinterface\n"));
}

TEST(InterfaceParsing, PackageImportInAnsiHeaderWithParamPortList) {
  EXPECT_TRUE(
      ParseOk("package pkg; parameter int W = 8; endpackage\n"
              "interface ifc import pkg::*; #(parameter int N = 4) ();\n"
              "endinterface\n"));
}

TEST(ModuleHeaderDefinition, AnsiHeaderPackageImportRequiresPortList) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m import pkg::*;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(InterfaceParsing, AnsiHeaderPackageImportRequiresPortList) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "interface ifc import pkg::*;\n"
      "endinterface\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ModuleHeaderDefinition, AnsiHeaderPackageImportFollowedByEmptyPortList) {
  EXPECT_TRUE(
      ParseOk("package pkg; endpackage\n"
              "module m import pkg::*; ();\n"
              "endmodule\n"));
}

TEST(ModuleHeaderDefinition, AnsiHeaderTwoSeparatePackageImports) {
  auto r = Parse(
      "package a; endpackage\n"
      "package b; endpackage\n"
      "module m import a::*; import b::*; ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(r.cu->modules[0]->items[1]->kind, ModuleItemKind::kImportDecl);
}

}  // namespace
