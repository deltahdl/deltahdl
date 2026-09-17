#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// 18.5.11: the clause's count_ones, a function looping over the bits of its
// argument, called in a constraint holding length to the count: the function
// is called before the constraints are solved with v drawn first, and its
// return value is the state variable length is held to, so over 32 draws
// length equals the ones the module counts in v on every draw, as the
// design test/src/e2e/functions_in_constraints.sv runs it.
TEST(FunctionsInConstraintsRun, ALoopingFunctionCountsTheOnesOfItsArgument) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [9:0] v;\n"
      "  rand int length;\n"
      "  constraint C1 { length == count_ones(v); }\n"
      "  function int count_ones(bit [9:0] w);\n"
      "    int n;\n"
      "    for (n = 0; w != 0; w = w >> 1)\n"
      "      n += w & 1'b1;\n"
      "    return n;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0, ones = 0, varied = 0, first = -1;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    repeat (32) begin\n"
      "      void'(o.randomize());\n"
      "      ones = 0;\n"
      "      for (int i = 0; i < 10; i++) if (o.v[i]) ones++;\n"
      "      if (o.length == ones) held++;\n"
      "      if (first < 0) first = ones;\n"
      "      else if (ones != first) varied = 1;\n"
      "    end\n"
      "    $display(\"%0d %0d\", held, varied);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 1\n");
}

// 18.5.11: the clause's B, x at most F(y) under y inside {2, 4, 8}: y, a
// function argument, is solved first from its own constraint, so over 600
// draws each of 2, 4 and 8 comes up in near a third of them, where a joint
// draw over the legal combinations of a 5-bit x at most three times y would
// give 8, which admits 25 of the 45 combinations, over half of the draws;
// and x is at most three times y on every draw.
TEST(FunctionsInConstraintsRun, TheArgumentIsSolvedFirstFromItsOwnSet) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [4:0] x;\n"
      "  rand int y;\n"
      "  constraint C { x <= F(y); }\n"
      "  constraint D { y inside {2, 4, 8}; }\n"
      "  function int F(int a);\n"
      "    return 3 * a;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0, twos = 0, eights = 0;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    repeat (600) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x <= 3 * o.y) held++;\n"
      "      if (o.y == 2) twos++;\n"
      "      if (o.y == 8) eights++;\n"
      "    end\n"
      "    $display(\"%0d %0d %0d\", held, twos > 130 && twos < 270,\n"
      "             eights > 130 && eights < 270);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "600 1 1\n");
}

}  // namespace
