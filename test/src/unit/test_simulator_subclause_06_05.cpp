#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

TEST(NetsAndVariablesSim, ForceOverridesANetAndReleaseRestoresItsResolved) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "  assign w = 1'bz;\n"
      "  initial begin\n"
      "    #1 $display(\"%b\", w);\n"
      "    force w = 1'b0;\n"
      "    #1 $display(\"%b\", w);\n"
      "    release w;\n"
      "    #1 $display(\"%b\", w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n0\n1\n");
}

TEST(NetsAndVariablesSim, VariableDrivesThePortNetOnTheOtherSide) {
  SimFixture f;
  std::string out = RunCapture(
      "module sub(input wire p, output wire q);\n"
      "  assign q = ~p;\n"
      "endmodule\n"
      "module m;\n"
      "  logic v = 1'b0;\n"
      "  wire o;\n"
      "  sub s(.p(v), .q(o));\n"
      "  initial begin\n"
      "    #1 $display(\"%b\", o);\n"
      "    v = 1'b1;\n"
      "    #1 $display(\"%b\", o);\n"
      "    v = 1'bx;\n"
      "    #1 $display(\"%b\", o);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n0\nx\n");
}

}  // namespace
