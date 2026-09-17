#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// 18.6: the clause's SimpleSum, three 8-bit random variables under z == x +
// y, randomized through the built-in randomize(): the call returns 1 and
// sets the three to values satisfying the constraint at their width on
// every one of 32 draws, and the values differ across the draws, as the
// design test/src/e2e/randomization_methods.sv runs it.
TEST(RandomizationMethodsRun, TheBuiltInRandomizeSetsTheSimpleSum) {
  SimFixture f;
  std::string out = RunCapture(
      "class SimpleSum;\n"
      "  rand bit [7:0] x, y, z;\n"
      "  constraint c { z == x + y; }\n"
      "endclass\n"
      "module t;\n"
      "  int success = 0, held = 0, varied = 0, first_x = -1, sum;\n"
      "  initial begin\n"
      "    SimpleSum p = new;\n"
      "    repeat (32) begin\n"
      "      if (p.randomize() == 1) success++;\n"
      "      sum = (p.x + p.y) & 255;\n"
      "      if (p.z == sum) held++;\n"
      "      if (first_x < 0) first_x = p.x;\n"
      "      else if (p.x != first_x) varied = 1;\n"
      "    end\n"
      "    $display(\"%0d %0d %0d\", success, held, varied);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32 1\n");
}

// 18.6.1: the value of a state variable can render a seemingly simple
// constraint unsatisfiable. With floor at 256 no 8-bit z lies at or above
// it, so randomize() returns 0 rather than drawing the bound the range was
// collapsed onto, which the declared range excludes; 18.6.3: z retains its
// previous value, pre_randomize() ran and post_randomize() did not.
TEST(RandomizationMethodsRun, AStateVariableCanMakeTheConstraintsInfeasible) {
  SimFixture f;
  std::string out = RunCapture(
      "class Counted;\n"
      "  rand bit [7:0] z;\n"
      "  int floor = 0;\n"
      "  int pre_calls = 0;\n"
      "  int post_calls = 0;\n"
      "  constraint bounded { z >= floor; }\n"
      "  function void pre_randomize();\n"
      "    pre_calls++;\n"
      "  endfunction\n"
      "  function void post_randomize();\n"
      "    post_calls++;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    Counted q = new;\n"
      "    q.z = 42;\n"
      "    q.floor = 256;\n"
      "    ok = q.randomize();\n"
      "    $display(\"%0d %0d %0d %0d\", ok, q.z, q.pre_calls, q.post_calls);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 42 1 0\n");
}

}  // namespace
