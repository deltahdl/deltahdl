#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ImplicitNamedPortConnectionSimulation, ImplicitInputPropagatesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  assign a = 8'hAB;\n"
      "  child u0(.a, .b);\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(ImplicitNamedPortConnectionSimulation, MixedImplicitAndExplicitPropagate) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input logic [7:0] a, input logic [7:0] b,\n"
      "             output logic [7:0] c);\n"
      "  assign c = a + b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, c;\n"
      "  assign a = 8'd10;\n"
      "  child u0(.a, .b(8'd20), .c);\n"
      "endmodule\n",
      f, "c");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(ImplicitNamedPortConnectionSimulation,
     ImplicitConnectionUsesSignalNotDefault) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input logic [7:0] a = 8'hFF, output logic [7:0] q);\n"
      "  assign q = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, q;\n"
      "  assign a = 8'h0A;\n"
      "  child u0(.a, .q);\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0Au);
}

TEST(ImplicitNamedPortConnectionSimulation,
     ImplicitConnectionPropagatesNetOperand) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input logic [7:0] a, output logic [7:0] q);\n"
      "  assign q = a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] a;\n"
      "  logic [7:0] q;\n"
      "  assign a = 8'h3C;\n"
      "  child u0(.a, .q);\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x3Cu);
}

TEST(ImplicitNamedPortConnectionSimulation, ConnectionReachesAnImportedName) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package p;\n"
                 "  logic [7:0] a = 8'h3C;\n"
                 "  logic [7:0] b = 8'h5A;\n"
                 "endpackage\n"
                 "module child(input logic [7:0] a, input logic [7:0] b);\n"
                 "  initial #1 $display(\"%h %h\", a, b);\n"
                 "endmodule\n"
                 "module top;\n"
                 "  import p::a;\n"
                 "  import p::*;\n"
                 "  child u0(.a, .b);\n"
                 "endmodule\n",
                 f),
      "3c 5a\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
