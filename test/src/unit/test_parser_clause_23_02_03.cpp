#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParameterizedModules, AnsiHeaderWithParams) {
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

TEST(ParameterizedModules, ModuleWithParameters) {
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

TEST(ParameterizedModules, LocalparamInParamPortList) {
  auto r = Parse(
      "module m #(parameter W = 8, localparam D = W*2)(\n"
      "  input logic [D-1:0] data\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParameterizedModules, NonAnsiHeaderWithParams) {
  auto r = Parse(
      "module m #(parameter int W = 8)(a, b);\n"
      "  input [W-1:0] a;\n"
      "  output [W-1:0] b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

TEST(ParameterizedModules, NonAnsiMultipleParamsWithRange) {
  auto r = Parse(
      "module generic_fifo (clk, read, write, reset, out, full, empty);\n"
      "  parameter MSB=3, LSB=0, DEPTH=4;\n"
      "  input [MSB:LSB] in;\n"
      "  input clk, read, write, reset;\n"
      "  output [MSB:LSB] out;\n"
      "  output full, empty;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->name, "generic_fifo");
}

TEST(ParameterizedModules, AnsiMultipleParamsWithMixedPorts) {
  auto r = Parse(
      "module generic_fifo\n"
      "  #(parameter MSB=3, LSB=0, DEPTH=4)\n"
      "  (input wire [MSB:LSB] in,\n"
      "   input wire clk, read, write, reset,\n"
      "   output logic [MSB:LSB] out,\n"
      "   output logic full, empty);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "generic_fifo");
  ASSERT_EQ(mod->params.size(), 3u);
  EXPECT_EQ(mod->params[0].first, "MSB");
  EXPECT_EQ(mod->params[1].first, "LSB");
  EXPECT_EQ(mod->params[2].first, "DEPTH");
}

TEST(ParameterizedModules, LocalparamDerivedFromParameterViaExpression) {
  auto r = Parse(
      "module generic_decoder\n"
      "  #(num_code_bits = 3,\n"
      "    localparam num_out_bits = 1 << num_code_bits)\n"
      "  (input [num_code_bits-1:0] A,\n"
      "   output reg [num_out_bits-1:0] Y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "generic_decoder");
  ASSERT_EQ(mod->params.size(), 2u);
  EXPECT_EQ(mod->params[0].first, "num_code_bits");
  EXPECT_EQ(mod->params[1].first, "num_out_bits");
  ASSERT_EQ(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].name, "A");
  EXPECT_EQ(mod->ports[1].name, "Y");
}

}  // namespace
