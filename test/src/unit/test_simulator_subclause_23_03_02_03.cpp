
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
  // 23.3.2.3: an implicit .name connection binds the like-named signal, so the
  // input port's specified default is not used even when one exists. Give the
  // signal a value that differs from the default and observe at run time that
  // the port -- echoed to an output -- carries the signal's value (0x0A), not
  // the default (0xFF). This is the runtime counterpart to the elaborator's
  // structural check that the binding is the signal and not the default.
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
  // 23.3.2.3: the like-named signal an implicit .name binds may be a net rather
  // than a variable. Drive a wire in the instantiating module and observe the
  // value reaching the input port through the implicit connection -- the net
  // operand form of the connection, distinct from the variable operand covered
  // by ImplicitInputPropagatesValue.
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

// §23.3.2.3: a `.name` connection is in error only where the name is neither
// declared nor imported, so one names a package variable an explicit import
// brings in, and one a wildcard import does, the connection itself being the
// reference that imports the candidate (§26.3); each port reads its value.
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
