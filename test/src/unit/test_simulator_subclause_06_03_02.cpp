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

// $typename names the data type alone, so each net carrying a strength names
// the type the same net declared without one names. The vector pair is named
// in full, a name no fallback to plain `logic` would give, and the signed pair
// is compared with each other: #9006 has a signed net's name leave out signed.
TEST(NetStrengthSim, TypenameLeavesOutTheStrength) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic a = 1'b1;\n"
      "  wire (strong0, weak1) w = a;\n"
      "  wire p = a;\n"
      "  trireg (large) c;\n"
      "  trireg c0;\n"
      "  trireg (large) [3:0] v4;\n"
      "  trireg [3:0] v5;\n"
      "  trireg (small) signed [3:0] cap2;\n"
      "  trireg signed [3:0] cap3;\n"
      "  initial begin\n"
      "    $display(\"%s %s\", $typename(w), $typename(p));\n"
      "    $display(\"%s %s\", $typename(c), $typename(c0));\n"
      "    $display(\"%s %s\", $typename(v4), $typename(v5));\n"
      "    $display(\"%0d\", $typename(cap2) == $typename(cap3));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "logic logic\nlogic logic\nlogic[3:0] logic[3:0]\n1\n");
}

// $bits counts the bits of the data type, and a strength adds none: each net
// carrying one is as wide as the same net declared without it. #9007 holds
// the type operator's comparisons of a net's type.
TEST(NetStrengthSim, BitsLeaveOutTheStrength) {
  const std::string kSrc =
      "module t;\n"
      "  logic a = 1'b1;\n"
      "  wire (strong0, weak1) w = a;\n"
      "  trireg (large) c;\n"
      "  trireg (small) signed [3:0] cap2;\n"
      "  trireg signed [3:0] cap3;\n"
      "  int r;\n"
      "  initial r = {$bits(w) == 1, $bits(c) == 1, $bits(cap2) == 4,\n"
      "               $bits(cap2) == $bits(cap3)};\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b1111u);
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
