// §6.3.2 keeps the strength information a net's bits carry out of the net's
// data type. A net declared with a drive strength, and a trireg declared with a
// charge strength, have the data type of the same net declared without one,
// and a value read from such a net is a value of that type, with no strength.
// The strength stays on the net's own bits, where %v still finds it.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// $typename names the data type alone. Each net carrying a strength is named
// as the same net without one and as the type written out, and the signed
// forms make the comparison one a fallback to plain `logic` would fail.
TEST(NetStrengthSim, TypenameLeavesOutTheStrength) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic a = 1'b1;\n"
      "  wire (strong0, weak1) logic signed ws = a;\n"
      "  wire logic signed ps = a;\n"
      "  trireg (large) c;\n"
      "  trireg (small) signed [3:0] cap2;\n"
      "  trireg signed [3:0] cap3;\n"
      "  initial begin\n"
      "    $display(\"%0d\", $typename(ws) == $typename(ps));\n"
      "    $display(\"%0d\", $typename(ws) == $typename(logic signed));\n"
      "    $display(\"%0d\", $typename(c) == $typename(logic));\n"
      "    $display(\"%0d\", $typename(cap2) == $typename(cap3));\n"
      "    $display(\"%0d\",\n"
      "             $typename(cap2) == $typename(logic signed [3:0]));\n"
      "    $display(\"%0d\", $typename(cap2) == $typename(logic [3:0]));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n1\n1\n1\n1\n0\n");
}

// A type comparison and $bits read the same data type: each net carrying a
// strength matches the type written without one and holds its width, while
// the unsigned type beside the signed trireg does not match it.
TEST(NetStrengthSim, TypeComparisonAndBitsLeaveOutTheStrength) {
  const std::string kSrc =
      "module t;\n"
      "  logic a = 1'b1;\n"
      "  wire (strong0, weak1) w = a;\n"
      "  trireg (large) c;\n"
      "  trireg (small) signed [3:0] cap2;\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = {type(w) == type(logic), type(c) == type(logic),\n"
      "         type(cap2) == type(logic signed [3:0]),\n"
      "         type(cap2) == type(logic [3:0]),\n"
      "         $bits(w) == 1, $bits(c) == 1, $bits(cap2) == 4};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b1110111u);
}

// The weak 1 stays on the net's bit, where %v renders it, but a value read from
// the net is a plain 1. Driven on by a continuous assignment with no strength
// of its own, directly, through a function's argument or through a variable,
// it reaches each other net at the default strong strength.
TEST(NetStrengthSim, ValueReadFromTheNetCarriesNoStrength) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic a = 1'b1;\n"
      "  wire (strong0, weak1) w = a;\n"
      "  wire direct, through_call, through_var;\n"
      "  logic v;\n"
      "  function automatic logic pass(logic x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  assign direct = w;\n"
      "  assign through_call = pass(w);\n"
      "  always @* v = w;\n"
      "  assign through_var = v;\n"
      "  initial #1 $display(\"%v %v %v %v %b\", w, direct, through_call,\n"
      "                      through_var, v);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "We1 St1 St1 St1 1\n");
}

}  // namespace
