// §25.3.2

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(InterfaceDeclaration, WithVariables) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic req, gnt;\n"
      "  logic [7:0] addr, data;\n"
      "  logic [1:0] mode;\n"
      "  logic start, rdy;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->interfaces[0]->items.empty());
}

TEST(InterfaceDeclaration, WithNets) {
  auto r = Parse(
      "interface ifc;\n"
      "  wire valid;\n"
      "  wire [7:0] bus;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kNetDecl));
}

TEST(InterfaceDeclaration, SimpleBusExample) {
  auto r = Parse(
      "interface simple_bus(input logic clk);\n"
      "  logic req, gnt;\n"
      "  logic [7:0] addr, data;\n"
      "  logic [1:0] mode;\n"
      "  logic start, rdy;\n"
      "endinterface: simple_bus\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "simple_bus");
  EXPECT_EQ(r.cu->interfaces[0]->ports.size(), 1u);
  EXPECT_FALSE(r.cu->interfaces[0]->items.empty());
}

TEST(InterfaceDeclaration, SimpleBusUsageInModules) {
  EXPECT_TRUE(
      ParseOk("interface simple_bus(input logic clk);\n"
              "  logic req, gnt;\n"
              "  logic [7:0] addr, data;\n"
              "  logic [1:0] mode;\n"
              "  logic start, rdy;\n"
              "endinterface: simple_bus\n"
              "module memMod(simple_bus a);\n"
              "  logic avail;\n"
              "  always @(posedge a.clk) a.gnt <= a.req & avail;\n"
              "endmodule\n"));
}

TEST(InterfaceDeclaration, InstantiationInModule) {
  EXPECT_TRUE(
      ParseOk("interface simple_bus(input logic clk);\n"
              "  logic req, gnt;\n"
              "endinterface\n"
              "module top;\n"
              "  logic clk;\n"
              "  simple_bus sb_intf(.clk(clk));\n"
              "endmodule\n"));
}

TEST(InterfaceInstantiation, ModuleInstantiatesInterface) {
  EXPECT_TRUE(
      ParseOk("interface ifc; logic req; endinterface\n"
              "module m;\n"
              "  ifc u0();\n"
              "endmodule\n"));
}

}  // namespace
