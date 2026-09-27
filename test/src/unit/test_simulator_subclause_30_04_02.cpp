#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SpecifyPathSim, SimpleParallelPathSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "  initial x = 8'd42;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §30.4 defines a module path as "a connection between a source signal and a
// destination signal", and §30.4.1 makes the destination "a net or variable
// that is connected to a module output port or inout port". The destination is
// therefore a net, and §10.3.2 lets a continuous assignment drive one by naming
// a select of it, so the path delay applies to that driver as much as to one
// written on the whole name.
//
// The design below declares one path and drives one bit of its destination.
// `y[1]` rises six time units after `a[1]` does, so it still reads 0 at t=24
// and reads 1 at t=28. The delay was taken only where the left-hand side was a
// bare identifier, so this driver landed its bit at t=20 and the sample at 24
// read 1.
//
// `a` is driven through `sa` because §30.4.1 requires the path source to be a
// net connected to an input port, and an input port of a top module has no
// driver of its own; §23.3.3.3 admits the assignment onto it and it costs a
// delta cycle rather than simulation time.
TEST(SpecifyPathSim, BitSelectDriverOfAPathOutputTakesThePathDelay) {
  SimFixture f;
  std::string out = RunCapture(
      "module top(input [7:0] a, output [7:0] y);\n"
      "  logic [7:0] sa;\n"
      "  assign a = sa;\n"
      "  assign y[1] = a[1];\n"
      "  specify\n"
      "    (a => y) = 6;\n"
      "  endspecify\n"
      "  initial begin\n"
      "    sa = 8'h00;\n"
      "    #20 sa = 8'h02;\n"
      "  end\n"
      "  initial #24 $display(\"s24=%b\", y[1]);\n"
      "  initial #28 $display(\"s28=%b\", y[1]);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "s24=0\ns28=1\n");
}

// The same rule reached through a part-select, which names its net through the
// same base and so says the destination is recovered from the select rather
// than from a bit-select's own shape. `y[5:4]` follows `a[5:4]` six time units
// later, so the bit the stimulus moves reads 0 at t=24 and 1 at t=28.
TEST(SpecifyPathSim, PartSelectDriverOfAPathOutputTakesThePathDelay) {
  SimFixture f;
  std::string out = RunCapture(
      "module top(input [7:0] a, output [7:0] y);\n"
      "  logic [7:0] sa;\n"
      "  assign a = sa;\n"
      "  assign y[5:4] = a[5:4];\n"
      "  specify\n"
      "    (a => y) = 6;\n"
      "  endspecify\n"
      "  initial begin\n"
      "    sa = 8'h00;\n"
      "    #20 sa = 8'h10;\n"
      "  end\n"
      "  initial #24 $display(\"s24=%b\", y[4]);\n"
      "  initial #28 $display(\"s28=%b\", y[4]);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "s24=0\ns28=1\n");
}

// The discriminating half: a select-targeted driver of a net no module path
// names as its destination takes no path delay, in a module that declares a
// path onto another output. `z[1]` follows `a[1]` at once while `y[1]` waits
// the path's six units, so at t=22 the two read differently. A lookup that
// asked whether the design declared any path at all, rather than whether one
// names this net, would delay both.
TEST(SpecifyPathSim, SelectDriverOfANonPathNetTakesNoPathDelay) {
  SimFixture f;
  std::string out = RunCapture(
      "module top(input [7:0] a, output [7:0] y, output [7:0] z);\n"
      "  logic [7:0] sa;\n"
      "  assign a = sa;\n"
      "  assign y[1] = a[1];\n"
      "  assign z[1] = a[1];\n"
      "  specify\n"
      "    (a => y) = 6;\n"
      "  endspecify\n"
      "  initial begin\n"
      "    sa = 8'h00;\n"
      "    #20 sa = 8'h02;\n"
      "  end\n"
      "  initial #22 $display(\"y=%b z=%b\", y[1], z[1]);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "y=0 z=1\n");
}

// §30.4.2 (printed page 873): a path's input terminal may be
// `interface_identifier . port_identifier`, a signal of the module's interface
// port, so `(p.a => y) = 5` delays by 5 each transition of `y` that a change of
// `p.a` produces -- the connected instance's `a` rising at 10 and falling at
// 20. The path had kept the port name alone, starting at an `a` nothing in the
// module reads, and every transition landed undelayed.
TEST(SpecifyPathSim, InterfacePortSignalIsAPathSource) {
  SimFixture f;
  std::string out = RunCapture(
      "interface ifc;\n"
      "  logic a;\n"
      "endinterface\n"
      "module mybuf(ifc p, output y);\n"
      "  assign y = p.a;\n"
      "  specify\n"
      "    (p.a => y) = 5;\n"
      "  endspecify\n"
      "endmodule\n"
      "module top;\n"
      "  ifc i();\n"
      "  wire ty;\n"
      "  mybuf u(.p(i), .y(ty));\n"
      "  always @(ty) if ($time >= 8) $display(\"t=%0t y=%b\", $time, ty);\n"
      "  initial begin\n"
      "    i.a = 0;\n"
      "    #10 i.a = 1;\n"
      "    #10 i.a = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "t=15 y=1\n"
            "t=25 y=0\n");
}

// §25.3 with §10.3.2: the continuous assignment `assign y = p.a` reads through
// the interface port, so without the path `y` follows the connected
// instance's `a` at the moment it changes.
TEST(SpecifyPathSim, AssignReadingAnInterfacePortFollowsIt) {
  SimFixture f;
  std::string out = RunCapture(
      "interface ifc;\n"
      "  logic a;\n"
      "endinterface\n"
      "module mybuf(ifc p, output y);\n"
      "  assign y = p.a;\n"
      "endmodule\n"
      "module top;\n"
      "  ifc i();\n"
      "  wire ty;\n"
      "  mybuf u(.p(i), .y(ty));\n"
      "  always @(ty) if ($time >= 8) $display(\"t=%0t y=%b\", $time, ty);\n"
      "  initial begin\n"
      "    i.a = 0;\n"
      "    #10 i.a = 1;\n"
      "    #10 i.a = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "t=10 y=1\n"
            "t=20 y=0\n");
}

// §30.4.2 (printed page 873): Syntax 30-3's specify_input_terminal_descriptor
// and specify_output_terminal_descriptor are `identifier [ [
// constant_range_expression ] ]`, so a terminal may be a bit-select of a
// vector port, and `(a[0] => y[0]) = 2; (a[1] => y[1]) = 5` are two paths,
// each bit taking its own path's delay. The two collapsed into the last path
// declared and bit 0 moved after 5.
TEST(SimpleModulePathRun, BitSelectTerminalsDeclareOnePathPerBit) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module mybus(input [1:0] a, output [1:0] y);\n"
                       "  assign y = a;\n"
                       "  specify\n"
                       "    (a[0] => y[0]) = 2;\n"
                       "    (a[1] => y[1]) = 5;\n"
                       "  endspecify\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic [1:0] a;\n"
                       "  wire [1:0] ty;\n"
                       "  mybus u(.a(a), .y(ty));\n"
                       "  always @(ty) if ($time >= 8)\n"
                       "    $display(\"t=%0t y=%b\", $time, ty);\n"
                       "  initial begin\n"
                       "    a = 2'b00;\n"
                       "    #10 a[0] = 1;\n"
                       "    #10 a[1] = 1;\n"
                       "    #10 a[0] = 0;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=12 y=01\nt=25 y=11\nt=32 y=10\n");
}

}  // namespace
