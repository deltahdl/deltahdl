// Non-LRM tests

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA212, OutputUnpackedDim) {
  auto r = Parse("module m(output logic q [1:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ParserA212, InputUnpackedDim) {
  auto r = Parse("module m(input logic d [3:0]); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_FALSE(port.unpacked_dims.empty());
}

TEST(ParserSection23, Sec23_2_2_AnsiPortDirections) {
  auto r = Parse(
      "module m (input logic a, output logic y,\n"
      "          inout wire [7:0] data, ref logic [3:0] r);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 4u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "y");
  EXPECT_EQ(r.cu->modules[0]->ports[2].direction, Direction::kInout);
  EXPECT_EQ(r.cu->modules[0]->ports[2].name, "data");
  EXPECT_EQ(r.cu->modules[0]->ports[3].direction, Direction::kRef);
  EXPECT_EQ(r.cu->modules[0]->ports[3].name, "r");
}

TEST(ParserSection23, Sec23_2_2_EmptyPortsAndMiscVariants) {
  auto r1 = Parse("module m (); endmodule\n");
  ASSERT_NE(r1.cu, nullptr);
  EXPECT_FALSE(r1.has_errors);
  EXPECT_EQ(r1.cu->modules[0]->ports.size(), 0u);
  auto r2 = Parse("module m; endmodule\n");
  ASSERT_NE(r2.cu, nullptr);
  EXPECT_FALSE(r2.has_errors);
  EXPECT_EQ(r2.cu->modules[0]->ports.size(), 0u);
  EXPECT_TRUE(ParseOk("module m (.*); endmodule\n"));
  EXPECT_TRUE(ParseOk("module m (input int x = 10); endmodule\n"));

  EXPECT_TRUE(ParseOk("module m (input var int in1); endmodule\n"));
  EXPECT_TRUE(ParseOk("module m (output reg [7:0] q); endmodule\n"));
  EXPECT_TRUE(ParseOk("module m (input signed [7:0] s); endmodule\n"));

  EXPECT_TRUE(ParseOk("macromodule mm; endmodule\n"));
}

TEST(ParserSection23, ModuleEmptyPortList) {
  auto r = Parse("module m(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
}

TEST(ParserSection23, ModuleNoPortList) {
  auto r = Parse("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
}

TEST(ParserSection23, AnsiPortsInputOutput) {
  auto r = Parse(
      "module m(input logic clk, input logic rst, output logic q);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 3u);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[0].name, "clk");
  EXPECT_EQ(mod->ports[2].direction, Direction::kOutput);
  EXPECT_EQ(mod->ports[2].name, "q");
}

TEST(ParserSection23, AnsiPortsInout) {
  auto r = Parse(
      "module m(inout wire [7:0] data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInout);
  EXPECT_EQ(mod->ports[0].name, "data");
}

TEST(ParserSection23, AnsiHeaderWithParams) {
  auto r = Parse(
      "module m #(parameter N = 8) (input logic [N-1:0] data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  ASSERT_EQ(mod->params.size(), 1);
  EXPECT_EQ(mod->params[0].first, "N");
  ASSERT_EQ(mod->ports.size(), 1);
  EXPECT_EQ(mod->ports[0].name, "data");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
}

TEST(ParserSection23, AnsiHeaderEmptyParenPorts) {
  auto r = Parse("module m (); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
}

// list_of_port_declarations — ANSI form
TEST(ModuleParamsA13, AnsiPortDeclarations) {
  auto r = Parse(
      "module m(\n"
      "  input  logic       clk,\n"
      "  input  logic       rst,\n"
      "  output logic [7:0] data\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 3u);
}

// port_declaration with all four directions
TEST(ModuleParamsA13, AllPortDirections) {
  auto r = Parse(
      "module m(\n"
      "  input  logic a,\n"
      "  output logic b,\n"
      "  inout  wire  c,\n"
      "  ref    logic d\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 4u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].direction, Direction::kOutput);
  EXPECT_EQ(ports[2].direction, Direction::kInout);
  EXPECT_EQ(ports[3].direction, Direction::kRef);
}

// ansi_port_declaration with unpacked dimensions
TEST(ModuleParamsA13, AnsiPortUnpackedDim) {
  auto r = Parse(
      "module m(\n"
      "  input logic [7:0] data [4]\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// interface port header
TEST(ModuleParamsA13, InterfacePortHeader) {
  auto r = Parse(
      "module m(bus_if.master bus);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
