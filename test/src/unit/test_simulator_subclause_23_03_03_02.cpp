
#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PortConnectionRulesForVariablesSimulation,
     InputPortReceivesValueFromParent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] drv = 8'h42;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(drv), .b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x42u);
}

TEST(PortConnectionRulesForVariablesSimulation,
     OutputPortDrivesParentVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(output logic [7:0] y);\n"
      "  initial y = 8'h55;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.y(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x55u);
}

TEST(PortConnectionRulesForVariablesSimulation,
     UnconnectedInputVarTakesDataTypeDefault) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input var logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  // The input is a variable left unconnected, so it holds the default initial
  // value of its data type. For 4-state logic that default is x, which the
  // child forwards to result -- distinct from the high-Z an unconnected net
  // input would carry.
  EXPECT_EQ(var->value.ToString(), "xxxxxxxx");
}

TEST(PortConnectionRulesForVariablesSimulation, RefPortWriteReflectsInParent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(ref logic [7:0] v);\n"
      "  initial v = 8'hAB;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] shared;\n"
      "  child u(shared);\n"
      "endmodule\n",
      f, "shared");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// R1a admits any compatible expression on a variable input port, including a
// constant literal. The implied continuous assignment carries the literal into
// the port, and the child forwards it out, so the parent observes the constant.
TEST(PortConnectionRulesForVariablesSimulation,
     VariableInputPortReceivesLiteral) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input var logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(8'd7), .b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// R1a on a variable input port also admits a net operand, connected here by
// ordered (positional) list rather than by name. The net's value flows through
// the implied continuous assignment into the variable input port -- a net-to-
// variable connection whose compatibility is the §6.22.3 dependency in action.
TEST(PortConnectionRulesForVariablesSimulation,
     VariableInputPortReceivesNetPositional) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input var logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] w;\n"
      "  assign w = 8'h33;\n"
      "  logic [7:0] result;\n"
      "  child u(w, result);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x33u);
}

// R1d, 4-state half: the default is the data type's, so an unconnected 4-state
// variable input carries x rather than a value. This is the guard on the
// 2-state case below -- the rule is per type, not a blanket zero, and the two
// tests differ only in the port's type keyword.
TEST(PortConnectionRulesForVariablesSimulation,
     UnconnectedFourStateInputVarDefaultsToX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input var logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "xxxxxxxx");
}

// R1d: an unconnected variable input port takes the default initial value of
// its data type. For a 2-state type that default is 0, distinct from the x an
// unconnected 4-state variable input carries. This observes the data-type-
// dependent branch of the default rather than repeating the 4-state case.
TEST(PortConnectionRulesForVariablesSimulation,
     UnconnectedTwoStateInputVarDefaultsToZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input var bit [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "00000000");
}

// §23.3.3.2 (printed page 747): "References to the port variable shall be
// treated as hierarchical references to the variable to which it is connected
// in its instantiation", so a ref port drives nothing: the parent's v keeps
// its initializer 10, the parent writes 20 after the child read 10, the child
// reads that 20, and its r + 11 lands in v as 31. The connection was recorded
// as an output port's, and v's initializer and the parent's write were
// refused as a second driver.
TEST(RefPortSimulation, WritesOnEitherSideAreSeenOnTheOther) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child(ref int r);\n"
                       "  initial begin\n"
                       "    #1 $display(\"child %0d\", r);\n"
                       "    #2 $display(\"child2 %0d\", r);\n"
                       "    r = r + 11;\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  int v = 10;\n"
                       "  child c(.r(v));\n"
                       "  initial begin\n"
                       "    #2 v = 20;\n"
                       "    $display(\"parent %0d\", v);\n"
                       "    #2 $display(\"final %0d\", v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "child 10\nparent 20\nchild2 20\nfinal 31\n");
}

// A ref port beside input, output and inout ports, connected to a parent
// variable with an initializer: the child's write of 42 is the parent's r.
TEST(RefPortSimulation, RefPortBesideTheOtherDirections) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child(input logic [7:0] a, b, output logic "
                       "[7:0] s, inout wire io, ref int r);\n"
                       "  assign s = a + b;\n"
                       "  assign io = 1'b1;\n"
                       "  initial #1 r = 42;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic [7:0] s;\n"
                       "  wire io;\n"
                       "  int r = 0;\n"
                       "  child c(.a(8'd5), .b(8'd7), .s(s), .io(io), .r(r));\n"
                       "  initial #2 $display(\"sum %0d r %0d io %0d\", s, r, "
                       "io);\n"
                       "endmodule\n",
                       f),
            "sum 12 r 42 io 1\n");
}

}  // namespace
