// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// list_of_ports ::= ( port { , port } )  — non-ANSI
TEST(ModuleParamsA13, NonAnsiPorts) {
  auto r = Parse(
      "module m(a, b, y);\n"
      "  input a, b;\n"
      "  output y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_GE(r.cu->modules[0]->ports.size(), 3u);
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

// ansi_port_declaration with default value
TEST(ModuleParamsA13, AnsiPortWithDefault) {
  auto r = Parse(
      "module m(\n"
      "  input logic clk,\n"
      "  input logic rst = 0\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_NE(r.cu->modules[0]->ports[1].default_value, nullptr);
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
