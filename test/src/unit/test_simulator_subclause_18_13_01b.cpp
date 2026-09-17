#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// 18.13.1: the seed selects the sequence and the same seed yields the same
// sequence every time, whatever integral expression carries it: a literal
// 254, a parameter of 254, the expression 250 + 4 and a variable holding 254
// each replay all eight numbers the literal's sequence began with, and 255
// selects a different sequence, as the design test/src/e2e/urandom_function.sv
// runs it.
TEST(UrandomRun, TheSameSeedFromAnyIntegralExpressionReplaysTheSequence) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  parameter int SEED = 254;\n"
      "  int unsigned a[8], b[8];\n"
      "  int i, sv = 254, same = 0, diverged = 0;\n"
      "  function automatic int agreeing();\n"
      "    int n = 0;\n"
      "    for (int j = 0; j < 8; j++) if (a[j] == b[j]) n++;\n"
      "    return n;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a[0] = $urandom(254);\n"
      "    for (i = 1; i < 8; i++) a[i] = $urandom;\n"
      "    b[0] = $urandom(SEED);\n"
      "    for (i = 1; i < 8; i++) b[i] = $urandom;\n"
      "    same += agreeing();\n"
      "    b[0] = $urandom(250 + 4);\n"
      "    for (i = 1; i < 8; i++) b[i] = $urandom;\n"
      "    same += agreeing();\n"
      "    b[0] = $urandom(sv);\n"
      "    for (i = 1; i < 8; i++) b[i] = $urandom;\n"
      "    same += agreeing();\n"
      "    b[0] = $urandom(255);\n"
      "    for (i = 1; i < 8; i++) b[i] = $urandom;\n"
      "    diverged = agreeing() < 8;\n"
      "    $display(\"%0d %0d\", same, diverged);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "24 1\n");
}

// 18.13.1: each call returns a new number, and the number is unsigned and 32
// bits wide, so 32 consecutive unseeded calls each differ from the last and an
// assignment of the call to a 64-bit variable leaves the upper 32 bits zero
// on every one of 32 draws while the top bit of the 32 is set in some, which
// a signed result would have carried into the upper half.
TEST(UrandomRun, EachCallIsANewUnsignedThirtyTwoBitNumber) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [63:0] wide;\n"
      "  int unsigned r, prev;\n"
      "  int i, advanced = 0, upper_zero = 0, high = 0;\n"
      "  initial begin\n"
      "    prev = $urandom;\n"
      "    for (i = 0; i < 32; i++) begin\n"
      "      r = $urandom;\n"
      "      if (r != prev) advanced++;\n"
      "      prev = r;\n"
      "      wide = $urandom;\n"
      "      if (wide[63:32] == 0) upper_zero++;\n"
      "      if (wide[31]) high = 1;\n"
      "    end\n"
      "    $display(\"%0d %0d %0d\", advanced, upper_zero, high);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32 1\n");
}

}  // namespace
