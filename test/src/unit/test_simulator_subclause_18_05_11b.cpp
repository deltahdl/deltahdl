#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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
      "    static C o = new;\n"
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
      "    static C o = new;\n"
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
