#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

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
