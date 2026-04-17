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

TEST(InterfaceDeclaration, ModuleWithInterfaceAndScalarPort) {
  auto r = Parse(
      "interface simple_bus; logic req; endinterface\n"
      "module memMod(simple_bus a, input logic clk); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "clk");
}

TEST(InterfaceInstantiationInTop, PositionalConnectionToInterfacePort) {
  EXPECT_TRUE(
      ParseOk("interface simple_bus; logic req; endinterface\n"
              "module memMod(simple_bus a, input logic clk); endmodule\n"
              "module top;\n"
              "  logic clk = 0;\n"
              "  simple_bus sb_intf();\n"
              "  memMod mem(sb_intf, clk);\n"
              "endmodule\n"));
}

TEST(InterfaceInstantiationInTop, NamedConnectionToInterfacePort) {
  EXPECT_TRUE(
      ParseOk("interface simple_bus; logic req; endinterface\n"
              "module cpuMod(simple_bus b, input logic clk); endmodule\n"
              "module top;\n"
              "  logic clk = 0;\n"
              "  simple_bus sb_intf();\n"
              "  cpuMod cpu(.b(sb_intf), .clk(clk));\n"
              "endmodule\n"));
}

TEST(InterfaceInstantiationInTop, ImplicitConnectionToInterfacePort) {
  EXPECT_TRUE(
      ParseOk("interface simple_bus; logic req; endinterface\n"
              "module memMod(simple_bus sb_intf, input logic clk); endmodule\n"
              "module top;\n"
              "  logic clk = 0;\n"
              "  simple_bus sb_intf();\n"
              "  memMod mem(.*);\n"
              "endmodule\n"));
}

}  // namespace
