// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, InterfaceWithTask) {
  auto r = Parse(
      "interface ifc;\n"
      "  task do_transfer;\n"
      "  endtask\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kTaskDecl));
}

TEST(DesignBuildingBlockParsing, InterfaceWithInitialBlock) {
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

TEST(DesignBuildingBlockParsing, InterfaceWithAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("interface ifc;\n"
              "  logic clk, gnt, req;\n"
              "  always @(posedge clk) gnt <= req;\n"
              "endinterface\n"));
}

TEST(DesignBuildingBlockParsing, InterfaceWithContAssign) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic a;\n"
      "  wire b;\n"
      "  assign b = a;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kContAssign));
}

TEST(DesignBuildingBlockParsing, InterfaceWithModport) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic req, gnt;\n"
      "  modport master(output req, input gnt);\n"
      "  modport slave(input req, output gnt);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 2u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "master");
  EXPECT_EQ(r.cu->interfaces[0]->modports[1]->name, "slave");
}

TEST(DesignBuildingBlockParsing, ModportWithDirectionalPorts) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic a, b, c;\n"
      "  modport mp(input a, b, output c);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 3u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[2].direction, Direction::kOutput);
}

TEST(DesignBuildingBlockParsing, InterfaceWithPorts) {
  auto r = Parse(
      "interface ifc(input logic clk);\n"
      "  logic req, gnt;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->interfaces[0]->ports.size(), 1u);
}

TEST(DesignBuildingBlockParsing, SimpleBusExample) {
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

TEST(DesignBuildingBlockParsing, SimpleBusUsageInModules) {
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

TEST(DesignBuildingBlockParsing, InterfaceInstantiationInModule) {
  EXPECT_TRUE(
      ParseOk("interface simple_bus(input logic clk);\n"
              "  logic req, gnt;\n"
              "endinterface\n"
              "module top;\n"
              "  logic clk;\n"
              "  simple_bus sb_intf(.clk(clk));\n"
              "endmodule\n"));
}

TEST(DesignBuildingBlockParsing, InterfaceWithMixedContents) {
  EXPECT_TRUE(
      ParseOk("interface ifc #(parameter int W = 8) (input logic clk);\n"
              "  localparam int DEPTH = 4;\n"
              "  logic [W-1:0] data;\n"
              "  wire valid;\n"
              "  function automatic int xform(int v); return v; endfunction\n"
              "  task send; endtask\n"
              "  assign valid = |data;\n"
              "  modport master(output data, input valid);\n"
              "  modport slave(input data, output valid);\n"
              "endinterface\n"));
}

}  // namespace
