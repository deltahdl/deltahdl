#include <string>

#include "fixture_simulator.h"
#include "fixture_specify.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
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

}  // namespace
