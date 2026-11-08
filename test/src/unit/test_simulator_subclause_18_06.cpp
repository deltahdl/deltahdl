#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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
      "    static SimpleSum p = new;\n"
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
      "    static Counted q = new;\n"
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
