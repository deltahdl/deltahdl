#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The Uniform of test/src/e2e/rand_modifier.sv, an unconstrained rand bit
// [7:0] y beside a rand real v held to 0.0 to 2.0, randomized 2048 times
// by an initial running `body` after each call and printing what it
// counted.
std::string Design(const std::string& body, const std::string& print) {
  return "class Uniform;\n"
         "  rand bit [7:0] y;\n"
         "  rand real v;\n"
         "  constraint c { v > 0.0 && v < 2.0; }\n"
         "endclass\n"
         "module t;\n"
         "  int counts[256];\n"
         "  initial begin\n"
         "    Uniform u = new;\n"
         "    int repeats = 0, lower = 0, upper = 0, most = 0, drawn = 0;\n"
         "    bit [7:0] last;\n"
         "    for (int i = 0; i < 2048; i++) begin\n"
         "      void'(u.randomize());\n" +
         body + "    end\n" + print +
         "  end\n"
         "endmodule\n";
}

// §18.4.1: an unconstrained 8-bit rand variable takes any value from 0 to
// 255 with equal probability, so 2048 draws reach at least 240 of the 256
// values, none more than three times its share of 8, and successive calls
// repeat a value about 1 in 256 times, within 24 repeats where 8 are
// expected.
TEST(RandModifierRun, AnIntegralVariableIsUniformOverItsRange) {
  SimFixture f;
  std::string out = RunCapture(
      Design("      counts[u.y]++;\n"
             "      if (i > 0 && u.y == last) repeats++;\n"
             "      last = u.y;\n",
             "    for (int k = 0; k < 256; k++) begin\n"
             "      if (counts[k] > 0) drawn++;\n"
             "      if (counts[k] > most) most = counts[k];\n"
             "    end\n"
             "    $display(\"%0d %0d %0d\", drawn >= 240, most <= 24, "
             "repeats <= 24);\n"),
      f);
  EXPECT_EQ(out, "1 1 1\n");
}

// §18.4.1: a rand real is uniformly distributed over its range, so of 2048
// draws of v the halves 0.0 to 1.0 and 1.0 to 2.0 receive counts within a
// sixth of each other, and every draw stays in the range.
TEST(RandModifierRun, ARealVariableIsUniformOverItsRange) {
  SimFixture f;
  std::string out = RunCapture(
      Design("      if (u.v < 1.0) lower++; else upper++;\n"
             "      if (u.v > 0.0 && u.v < 2.0) drawn++;\n",
             "    $display(\"%0d %0d\", (lower > upper ? lower - upper : "
             "upper - lower) <= 341, drawn == 2048);\n"),
      f);
  EXPECT_EQ(out, "1 1\n");
}

}  // namespace
