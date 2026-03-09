#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection4, Sec4_9_3_StaticModuleLifetime) {
  EXPECT_TRUE(
      ParseOk("module static m;\n"
              "  function int fn();\n"
              "    return 0;\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(ParserSection23, EndLabelModule) {
  auto r = Parse("module foo; endmodule : foo\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "foo");
}

TEST(ParserSection23, EndLabelModuleNoLabel) {
  auto r = Parse("module bar; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "bar");
}

TEST(ParserSection23, ModuleHeaderImport) {
  auto r = Parse(
      "module m import pkg::*; ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");

  ASSERT_GE(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kImportDecl);
}

TEST(ParserSection23, ModuleHeaderImportDetails) {
  auto r = Parse(
      "module m import pkg::*; ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->import_item.package_name, "pkg");
  EXPECT_TRUE(mod->items[0]->import_item.is_wildcard);
}

TEST(ParserSection23, ModuleHeaderImportWithParamsImport) {
  auto r = Parse(
      "module m import A::*; #(parameter N = 4) (input logic clk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  ASSERT_GE(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kImportDecl);
}

TEST(ParserSection23, ModuleHeaderImportWithParamsPortsAndParams) {
  auto r = Parse(
      "module m import A::*; #(parameter N = 4) (input logic clk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->params.size(), 1);
  ASSERT_EQ(mod->ports.size(), 1);
}

TEST(ParserSection23, ModuleHeaderMultipleImportsFirst) {
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

TEST(ParserSection23, ModuleWithParameters) {
  auto r = Parse(
      "module m #(parameter WIDTH = 8, parameter DEPTH = 16)(\n"
      "  input logic [WIDTH-1:0] data_in,\n"
      "  output logic [WIDTH-1:0] data_out\n"
      ");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  ASSERT_EQ(mod->params.size(), 2u);
  EXPECT_EQ(mod->params[0].first, "WIDTH");
  EXPECT_EQ(mod->params[1].first, "DEPTH");
  ASSERT_EQ(mod->ports.size(), 2u);
}

TEST(ParserSection23, ModuleDefinitionEmpty) {
  auto r = Parse("module empty_mod; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "empty_mod");
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}
TEST(ParserSection6, ModuleLifetimeAutomatic) {
  auto r = Parse("module automatic t; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "t");
}

TEST(ParserCh512, TopLevel_TrailingSemicolonAfterEndmodule) {
  EXPECT_TRUE(ParseOk("module m; endmodule;"));
}

TEST(ParserAnnexA, A1ModuleWithParams) {
  auto r = Parse(
      "module m #(parameter W = 8, parameter D = 4)(\n"
      "  input logic [W-1:0] data\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->params.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 1u);
}

TEST(ModuleParamsA13, EmptyParamPortList) {
  auto r = Parse("module m #(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->params.empty());
}

TEST(ModuleParamsA13, LocalparamInParamPortList) {
  auto r = Parse(
      "module m #(parameter W = 8, localparam D = W*2)(\n"
      "  input logic [D-1:0] data\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleEmptyPortList, ModuleEmptyPortList) {
  auto r = Parse("module m(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
}

TEST(ModuleNoPortList, ModuleNoPortList) {
  auto r = Parse("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
}

TEST(ModuleEmptyPortList, AnsiHeaderEmptyParenPorts) {
  auto r = Parse("module m (); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
}

}  // namespace
