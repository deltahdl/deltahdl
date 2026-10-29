// §6.5 (printed page 91) lets a continuous assignment drive a variable, and a
// primitive output or an output port connected to a variable is one. Whatever
// strength the driver carries, the variable takes the driven value converted
// to its own type, as an assignment converts it, and the strength is lost. A
// tool may warn of a strength other than St0, St1, StX or HiZ reaching a
// variable; none is an error. §10.3.4 keeps a drive strength written on an
// `assign` to scalar nets, so a strength reaches a variable through a gate, a
// UDP or a port.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// A gate written with a weak or a pull strength drives the variable's value,
// a 0 and a 1 each read back as the plain value.
TEST(StrengthLostOnAVariable, GateWithAStrengthDrivesTheValue) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  logic v0, v1;\n"
      "  buf (weak0, weak1) g0 (v0, a);\n"
      "  buf (pull0, pull1) g1 (v1, a);\n"
      "  initial begin\n"
      "    #1 $display(\"%b %b\", v0, v1);\n"
      "    a = 1'b1;\n"
      "    #1 $display(\"%b %b\", v0, v1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "0 0\n1 1\n");
}

// A highz strength drives no value on its side: the variable reads z there,
// the HiZ the rule names among what a variable may be driven with, and the
// driven value on the other side.
TEST(StrengthLostOnAVariable, HighzSideReachesTheVariableAsZ) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  logic v1, v0;\n"
      "  buf (strong0, highz1) g1 (v1, a);\n"
      "  buf (highz0, strong1) g0 (v0, a);\n"
      "  initial begin\n"
      "    #1 $display(\"%b %b\", v1, v0);\n"
      "    a = 1'b1;\n"
      "    #1 $display(\"%b %b\", v1, v0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "0 z\nz 1\n");
}

// A UDP instance carries its strength to the variable its output names the
// same way.
TEST(StrengthLostOnAVariable, UdpWithAStrengthDrivesTheValue) {
  SimFixture f;
  std::string out = RunCapture(
      "primitive inv(output o, input i);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  logic v, h;\n"
      "  inv (weak0, weak1) u (v, a);\n"
      "  inv (highz0, strong1) uh (h, a);\n"
      "  initial begin\n"
      "    #1 $display(\"%b %b\", v, h);\n"
      "    a = 1'b1;\n"
      "    #1 $display(\"%b %b\", v, h);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "1 1\n0 z\n");
}

// An output port connected to a variable implies a continuous assignment to
// it (§23.3.3), and the weak strength the port's net is driven with inside the
// instance does not reach the variable.
TEST(StrengthLostOnAVariable, OutputPortNetWithAStrengthDrivesTheValue) {
  SimFixture f;
  std::string out = RunCapture(
      "module src(output wire o, input logic d);\n"
      "  assign (weak0, weak1) o = d;\n"
      "endmodule\n"
      "module t;\n"
      "  logic d = 1'b1;\n"
      "  logic v;\n"
      "  src s(.o(v), .d(d));\n"
      "  initial begin\n"
      "    #1 $display(\"%b\", v);\n"
      "    d = 1'b0;\n"
      "    #1 $display(\"%b\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "1\n0\n");
}

// The nearest form the standard forbids: a drive strength written on an
// `assign` whose target is a variable, which §10.3.4 keeps to scalar nets.
TEST(StrengthLostOnAVariable, AssignmentStrengthOnAVariableIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic a, v;\n"
      "  assign (weak0, weak1) v = a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength not allowed on continuous assignment to a variable", 3,
      "10.3.4"));
}

// A 2-state variable converts an x or a z driven to it into 0, whether an
// assignment drives the x or a highz strength leaves the z, bit by bit in a
// vector.
TEST(StrengthLostOnAVariable, TwoStateVariableTakesZeroForXAndZ) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic a = 1'b1;\n"
      "  logic unknown = 1'bx;\n"
      "  bit bx, bz;\n"
      "  bit [3:0] bv;\n"
      "  assign bx = unknown;\n"
      "  buf (strong0, highz1) g (bz, a);\n"
      "  assign bv = 4'b1x0z;\n"
      "  initial #1 $display(\"%b %b %b\", bx, bz, bv);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "0 0 1000\n");
}

// The value converts to the variable's type as an assignment's does: an
// integer to a real numerically, a real to an integer rounded with ties away
// from zero (§6.12.1), a wider value truncated, and a narrower one extended
// by its own signedness.
TEST(StrengthLostOnAVariable, ValueConvertsToTheVariablesType) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  real r;\n"
      "  int up, down, from_unsigned, from_signed;\n"
      "  logic [7:0] narrow;\n"
      "  assign r = 7;\n"
      "  assign up = 2.6;\n"
      "  assign down = -2.5;\n"
      "  assign narrow = 12'hABC;\n"
      "  assign from_unsigned = 8'hFF;\n"
      "  assign from_signed = 8'shFF;\n"
      "  initial #1 $display(\"%0.1f %0d %0d %h %0d %0d\", r, up, down,\n"
      "                      narrow, from_unsigned, from_signed);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "7.0 3 -3 bc 255 -1\n");
}

// An input port connected to an expression is continuously assigned it
// (§23.3.3), so a variable port converts the value to its own type: an
// integer expression into a real port, a real one into an int port rounded
// with ties away from zero.
TEST(StrengthLostOnAVariable, InputPortVariableConvertsTheConnectedValue) {
  SimFixture f;
  std::string out = RunCapture(
      "module sub(input var real r, input var int i);\n"
      "  initial #1 $display(\"%0.1f %0d\", r, i);\n"
      "endmodule\n"
      "module t;\n"
      "  int k = 3;\n"
      "  real h = 2.5;\n"
      "  sub s(.r(k + 1), .i(h));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "4.0 3\n");
}

}  // namespace
