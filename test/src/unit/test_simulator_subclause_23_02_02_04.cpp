
#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(DefaultPortValueSimulation, OmittedInputUsesDefaultNamedConn) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input logic [7:0] a = 8'hFF, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(DefaultPortValueSimulation, ExplicitConnectionOverridesDefault) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input logic [7:0] a = 8'hFF, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(8'h42), .b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x42u);
}

TEST(DefaultPortValueSimulation, OrderedOmissionUsesDefault) {
  // §23.2.2.4: the general rule is that an input port with a default may be
  // omitted from the instantiation and the compiler inserts the default -- the
  // subclause's own worked example uses positional (ordered) instances with a
  // trailing input left off. The named-connection form is covered separately;
  // this exercises the ordered form. Here datain is the trailing port and is
  // omitted, so the child observes the declared default 8'hA5 and drives it
  // out.
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(output logic [7:0] dataout,\n"
      "             input logic [7:0] datain = 8'hA5);\n"
      "  assign dataout = datain;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(result);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(DefaultPortValueSimulation, DefaultFromLocalparamConstant) {
  // §23.2.2.4: a port default is a constant expression evaluated in the
  // defining module's scope. A literal and a compilation-unit parameter are
  // covered elsewhere; this covers the localparam form, which reaches the value
  // through a different declaration/resolution path (a localparam declared in
  // the child's own parameter port list). The default references W, so omitting
  // datain must drive W's value 8'h3C.
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child #(localparam logic [7:0] W = 8'h3C) (\n"
      "  output logic [7:0] dataout,\n"
      "  input logic [7:0] datain = W);\n"
      "  assign dataout = datain;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.dataout(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x3Cu);
}

TEST(DefaultPortValueSimulation, DefaultEvaluatedInDefiningModuleScope) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "parameter logic [7:0] My_DataIn = 8'hFF;\n"
      "module bus_conn (\n"
      "  output logic [7:0] dataout,\n"
      "  input        [7:0] datain = My_DataIn\n"
      ");\n"
      "  assign dataout = datain;\n"
      "endmodule\n"
      "module top;\n"
      "  parameter logic [7:0] My_DataIn = 8'h00;\n"
      "  logic [7:0] result;\n"
      "  bus_conn u(.dataout(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

// §23.2.2.4 with §6.12: a real port's default is a constant expression of
// the module declaring the port, folded as a real, so a real parameter of that
// module scaled by a real keeps its fraction, and an integer parameter plus a
// real fraction does too.
TEST(DefaultPortValueSimulation, RealDefaultReadsTheDefiningModulesParameter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub #(parameter real R = 2.5, parameter int K = "
                       "3)\n"
                       "  (input var real r = R * 2.0,\n"
                       "   input var real rk = K + 0.25);\n"
                       "  initial #1 $display(\"%f %f\", r, rk);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  sub s();\n"
                       "endmodule\n",
                       f),
            "5.000000 3.250000\n");
}

// §23.2.2.4 with §11.6.1: a default wider than 64 bits keeps every bit, one
// written as an expression of literals, one reading a parameter of the module
// declaring the port, and a signed one whose sign extends through them all.
TEST(DefaultPortValueSimulation, DefaultWiderThan64BitsKeepsEveryBit) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "module sub #(parameter logic signed [127:0] P = "
                "128'sh1 << 99)\n"
                "  (input var logic [127:0] w = 128'hF0 << 100,\n"
                "   input var logic [127:0] v = P | 128'h3,\n"
                "   input var logic signed [127:0] s = P - (128'sh1 << 100));\n"
                "  initial #1 $display(\"%h %h %h %0d\", w, v, s, s < 0);\n"
                "endmodule\n"
                "module top;\n"
                "  sub u();\n"
                "endmodule\n",
                f),
            "00000f00000000000000000000000000 00000008000000000000000000000003 "
            "fffffff8000000000000000000000000 1\n");
}

}  // namespace
