#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SourceText, InterfaceNonAnsiHeader) {
  auto r = Parse(
      "interface ifc(clk);\n"
      "  input clk;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports.size(), 1u);
}

TEST(InterfaceInstantiationGrammar, BasicInterfaceInst) {
  auto r = Parse("module m; my_if u0(.a(a), .b(b)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_EQ(item->inst_name, "u0");
}

TEST(InterfaceInstantiationGrammar, InterfaceInstWithParams) {
  auto r = Parse("module m; my_if #(8) u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_EQ(item->inst_name, "u0");
  ASSERT_EQ(item->inst_params.size(), 1u);
}

TEST(InterfaceParsing, EndinterfaceLabel) {
  auto r = Parse(
      "interface simple_bus;\n"
      "endinterface : simple_bus\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->name, "simple_bus");
}

TEST(InterfaceParsing, EndinterfaceNoLabel) {
  auto r = Parse(
      "interface my_if;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->name, "my_if");
}

TEST(InterfaceParsing, MultipleModportItems) {
  auto r = Parse(
      "interface bus;\n"
      "  logic a;\n"
      "  logic b;\n"
      "  modport m1(input a), m2(output b);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* iface = r.cu->interfaces[0];
  ASSERT_EQ(iface->modports.size(), 2);
  VerifyModportItem(iface->modports[0], "m1", Direction::kInput, "a");
  VerifyModportItem(iface->modports[1], "m2", Direction::kOutput, "b");
}

TEST(InterfaceParsing, MultipleModportThreeItems) {
  auto r = Parse(
      "interface bus;\n"
      "  logic a;\n"
      "  logic b;\n"
      "  logic c;\n"
      "  modport m1(input a), m2(output b), m3(inout c);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* iface = r.cu->interfaces[0];
  ASSERT_EQ(iface->modports.size(), 3);
  const std::string kExpectedNames[] = {"m1", "m2", "m3"};
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(iface->modports[i]->name, kExpectedNames[i]);
  }
  EXPECT_EQ(iface->modports[2]->ports[0].direction, Direction::kInout);
}

TEST(Parser, EmptyInterface) {
  auto r = Parse("interface simple_bus; endinterface");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->name, "simple_bus");
  EXPECT_EQ(r.cu->interfaces[0]->decl_kind, ModuleDeclKind::kInterface);
}

TEST(SourceText, InterfaceOrGenerateItemModuleCommon) {
  auto r = Parse(
      "interface ifc;\n"
      "  assign a = b;\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  ASSERT_GE(ifc->items.size(), 1u);
  EXPECT_EQ(ifc->items[0]->kind, ModuleItemKind::kContAssign);
}

TEST(SourceText, NonPortInterfaceItemGenerateRegion) {
  auto r = Parse(
      "interface ifc;\n"
      "  generate\n"
      "    assign a = b;\n"
      "  endgenerate\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_GE(r.cu->interfaces[0]->items.size(), 1u);
}

TEST(SourceText, NonPortInterfaceItemProgram) {
  auto r = Parse(
      "interface ifc;\n"
      "  program p; endprogram\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_GE(r.cu->interfaces[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->items[0]->kind,
            ModuleItemKind::kNestedModuleDecl);
}

TEST(SourceText, NonPortInterfaceItemNestedInterface) {
  auto r = Parse(
      "interface outer;\n"
      "  interface inner; endinterface\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_GE(r.cu->interfaces[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->items[0]->kind,
            ModuleItemKind::kNestedModuleDecl);
}

TEST(SourceText, NonPortInterfaceItemTimeunits) {
  auto r = Parse(
      "interface ifc;\n"
      "  timeunit 1ns;\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
}

TEST(SourceText, ExternInterface) {
  auto r = Parse("extern interface ifc(input logic clk);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_TRUE(r.cu->interfaces[0]->is_extern);
  EXPECT_EQ(r.cu->interfaces[0]->name, "ifc");
}

TEST(SourceText, InterfaceAnsiHeader) {
  auto r = Parse("interface ifc(input logic clk); endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports.size(), 1u);
}

TEST(SourceText, InterfaceWildcardPorts) {
  auto r = Parse("interface ifc(.*); endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_TRUE(r.cu->interfaces[0]->has_wildcard_ports);
}

TEST(SourceText, InterfaceParamsAndPorts) {
  auto r = Parse(
      "interface ifc #(parameter int W = 8)(input logic clk);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports.size(), 1u);
}

TEST(Parser, InterfaceWithPorts) {
  auto r = Parse(
      "interface bus(input logic clk, input logic rst);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->ports.size(), 2);
}

TEST(SourceText, InterfaceItemPortDecl) {
  auto r = Parse(
      "interface ifc(input logic clk, output logic data);\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].name, "clk");
  EXPECT_EQ(r.cu->interfaces[0]->ports[1].name, "data");
}

TEST(SourceText, NonPortInterfaceItemModport) {
  auto r = Parse(
      "interface ifc;\n"
      "  modport master(input clk, output data);\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "master");
}

TEST(InterfaceDeclParsing, AttrOnSimplePorts) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  logic a;\n"
              "  modport target((* synthesis *) input a);\n"
              "endinterface\n"));
}
TEST(ModuleAndHierarchyParsing, InterfaceLifetimeAutomatic) {
  auto r = Parse("interface automatic myif; endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->name, "myif");
}

TEST(InterfaceEndLabel, EndLabelMatchesInterfaceName) {
  auto r = Parse("interface baz; endinterface : baz\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "baz");
}

TEST(InterfaceDeclaration, MissingEndinterfaceIsError) {
  EXPECT_FALSE(ParseOk("interface i;"));
}

TEST(InterfaceDeclarations, InterfaceKeywordIntroducesInterface) {
  auto r = Parse("interface ifc; endinterface");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->decl_kind, ModuleDeclKind::kInterface);
}

TEST(InterfaceDeclarations, InterfaceContainsDeclarations) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic req, gnt;\n"
      "  logic [7:0] data;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->interfaces[0]->items.empty());
}

TEST(InterfaceDeclaration, EnclosedByKeywords) {
  auto r = Parse("interface ifc; endinterface");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "ifc");
  EXPECT_EQ(r.cu->interfaces[0]->decl_kind, ModuleDeclKind::kInterface);
}

TEST(InterfaceDeclaration, WithInitialBlock) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic flag;\n"
      "  initial flag = 0;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(InterfaceDeclaration, WithAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("interface ifc;\n"
              "  logic clk, gnt, req;\n"
              "  always @(posedge clk) gnt <= req;\n"
              "endinterface\n"));
}

}  // namespace
