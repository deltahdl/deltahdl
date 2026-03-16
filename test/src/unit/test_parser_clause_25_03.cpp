#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

}  // namespace
