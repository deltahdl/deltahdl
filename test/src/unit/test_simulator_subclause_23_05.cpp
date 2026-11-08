#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ExternModuleSimulation, ExternDoesNotInterfereWithSimulation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "extern module child(input logic [7:0] a, output logic [7:0] b);\n"
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  assign a = 8'hAB;\n"
      "  child u0(.a(a), .b(b));\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(ExternModuleSimulation, WildcardPortsFromExternSimulate) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "extern module child(input logic [7:0] a, output logic [7:0] b);\n"
      "module child(.*);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  assign a = 8'hCD;\n"
      "  child u0(.a(a), .b(b));\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

TEST(ExternModuleSimulation, NonAnsiExternWildcardSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "extern module gate(a, b, c, d);\n"
      "module gate(.*);\n"
      "  input a, b, c;\n"
      "  output d;\n"
      "  assign d = a & b & c;\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b, c, d;\n"
      "  assign a = 1'b1;\n"
      "  assign b = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  gate u0(.a(a), .b(b), .c(c), .d(d));\n"
      "endmodule\n",
      f, "d");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ExternModuleSimulation, ValueParameterizedExternWildcardSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "extern module widen #(parameter W = 4)\n"
      "  (input logic [W-1:0] a, output logic [W-1:0] b);\n"
      "module widen(.*);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [3:0] a, b;\n"
      "  assign a = 4'hA;\n"
      "  widen u0(.a(a), .b(b));\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

TEST(ExternModuleSimulation, TypeParameterizedExternWildcardSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "extern module conv #(parameter type TP = logic [7:0])\n"
      "  (input TP a, output TP b);\n"
      "module conv(.*);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  assign a = 8'h5A;\n"
      "  conv u0(.a(a), .b(b));\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5Au);
}

TEST(ExternModuleSimulation, NestedExternModuleSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  extern module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  module child(input logic [7:0] a, output logic [7:0] b);\n"
      "    assign b = a;\n"
      "  endmodule\n"
      "  assign a = 8'h3C;\n"
      "  child u0(.a(a), .b(b));\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x3Cu);
}

TEST(ExternModuleSimulation, WildcardExternUnpackedParameterPortIsArray) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "extern module a #(parameter int P [2] = '{3, 5}) (output int y);\n"
      "module a (.*);\n"
      "  assign y = P[1];\n"
      "endmodule\n"
      "module top;\n"
      "  int y;\n"
      "  a u (.y(y));\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

}  // namespace
