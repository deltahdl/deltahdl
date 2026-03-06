#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §3.5: Interfaces are enclosed between interface...endinterface.

TEST(ParserClause03, Cl3_5_InterfaceEnclosedByKeywords) {
  auto r = Parse("interface ifc; endinterface");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "ifc");
  EXPECT_EQ(r.cu->interfaces[0]->decl_kind, ModuleDeclKind::kInterface);
}

// --- Interface can have parameters, constants, variables ---

TEST(ParserClause03, Cl3_5_InterfaceWithParameters) {
  auto r = Parse(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->interfaces[0]->params.empty());
}

TEST(ParserClause03, Cl3_5_InterfaceWithConstants) {
  auto r = Parse(
      "interface ifc;\n"
      "  localparam int DEPTH = 16;\n"
      "  parameter int WIDTH = 8;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(
      CountItemsByKind(r.cu->interfaces[0]->items, ModuleItemKind::kParamDecl),
      1u);
}

TEST(ParserClause03, Cl3_5_InterfaceWithVariables) {
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

TEST(ParserClause03, Cl3_5_InterfaceWithNets) {
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

// --- Interface can have functions and tasks ---

TEST(ParserClause03, Cl3_5_InterfaceWithFunction) {
  auto r = Parse(
      "interface ifc;\n"
      "  function automatic int transform(int val);\n"
      "    return val + 1;\n"
      "  endfunction\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->interfaces[0]->items,
                             ModuleItemKind::kFunctionDecl));
}

TEST(ParserClause03, Cl3_5_InterfaceWithTask) {
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

// --- Interface can contain processes and continuous assignments ---

TEST(ParserClause03, Cl3_5_InterfaceWithInitialBlock) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic flag;\n"
      "  initial flag = 0;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->interfaces[0]->items,
                             ModuleItemKind::kInitialBlock));
}

TEST(ParserClause03, Cl3_5_InterfaceWithAlwaysBlock) {
  EXPECT_TRUE(ParseOk(
      "interface ifc;\n"
      "  logic clk, gnt, req;\n"
      "  always @(posedge clk) gnt <= req;\n"
      "endinterface\n"));
}

TEST(ParserClause03, Cl3_5_InterfaceWithContAssign) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic a;\n"
      "  wire b;\n"
      "  assign b = a;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->interfaces[0]->items,
                             ModuleItemKind::kContAssign));
}

// --- Modport construct ---

TEST(ParserClause03, Cl3_5_InterfaceWithModport) {
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

TEST(ParserClause03, Cl3_5_ModportWithDirectionalPorts) {
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

// --- Interface ports ---

TEST(ParserClause03, Cl3_5_InterfaceWithPorts) {
  auto r = Parse(
      "interface ifc(input logic clk);\n"
      "  logic req, gnt;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->interfaces[0]->ports.size(), 1u);
}

// --- LRM §3.5 simple_bus example ---

TEST(ParserClause03, Cl3_5_SimpleBusExample) {
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

TEST(ParserClause03, Cl3_5_SimpleBusUsageInModules) {
  EXPECT_TRUE(ParseOk(
      "interface simple_bus(input logic clk);\n"
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

TEST(ParserClause03, Cl3_5_InterfaceInstantiationInModule) {
  EXPECT_TRUE(ParseOk(
      "interface simple_bus(input logic clk);\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk;\n"
      "  simple_bus sb_intf(.clk(clk));\n"
      "endmodule\n"));
}

// --- Mixed contents ---

TEST(ParserClause03, Cl3_5_InterfaceWithMixedContents) {
  EXPECT_TRUE(ParseOk(
      "interface ifc #(parameter int W = 8) (input logic clk);\n"
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
