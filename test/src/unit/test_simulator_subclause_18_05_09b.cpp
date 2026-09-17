#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The clause's B, a 1-bit s implying a 32-bit d is zero, under the ordering
// constraints `order`, randomized 512 times by an initial that counts the
// draws with s set and the draws with s set and d nonzero, as the design
// test/src/e2e/variable_ordering.sv does.
std::string CountingSet(const std::string& order) {
  return "class B;\n"
         "  rand bit s;\n"
         "  rand bit [31:0] d;\n"
         "  constraint c { s -> d == 0; }\n" +
         order +
         "endclass\n"
         "module t;\n"
         "  int set = 0, wrong = 0;\n"
         "  initial begin\n"
         "    B o = new;\n"
         "    repeat (512) begin\n"
         "      void'(o.randomize());\n"
         "      if (o.s) set++;\n"
         "      if (o.s && o.d != 0) wrong++;\n"
         "    end\n"
         "    $display(\"%0d %0d\", set > 200 && set < 312, wrong);\n"
         "  end\n"
         "endmodule\n";
}

// 18.5.9: with no ordering the solver gives a uniform distribution over the
// legal value combinations, of which s is set in one of 1 + 2^32, so over
// 512 draws of the clause's B with a 32-bit d, s is set as good as never,
// which the 2-bit d of the earlier cases leaves at a fifth of the draws.
TEST(VariableOrderingRun, TheUnorderedControlIsAsGoodAsNeverSet) {
  SimFixture f;
  std::string out = RunCapture(
      "class B;\n"
      "  rand bit s;\n"
      "  rand bit [31:0] d;\n"
      "  constraint c { s -> d == 0; }\n"
      "endclass\n"
      "module t;\n"
      "  int set = 0;\n"
      "  initial begin\n"
      "    B o = new;\n"
      "    repeat (512) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.s) set++;\n"
      "    end\n"
      "    $display(\"%0d\", set);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

// 18.5.9: solve s before d has s chosen first, 0 or 1 with equal
// probability, and d then subject to it, so over 512 draws s is set near
// half the time, which a d of 32 bits drawn under s and tried against the
// implication would never allow, and d is zero on every draw with s set.
TEST(VariableOrderingRun, TheOrderedControlIsSetHalfTheTime) {
  SimFixture f;
  std::string out =
      RunCapture(CountingSet("  constraint order { solve s before d; }\n"), f);
  EXPECT_EQ(out, "1 0\n");
}

// 18.5.9: the variables may be solved in an order the ordering does not
// give where the outcome is the same: the clause's x held to 0 and below y
// under solve y before x has one assignment for x, so every one of 64
// solves succeeds with x at 0 and y above it, the ordering never making the
// solver fail.
TEST(VariableOrderingRun, AnOrderingNeverFailsTheSolve) {
  SimFixture f;
  std::string out = RunCapture(
      "class B;\n"
      "  rand bit [3:0] x;\n"
      "  rand bit [3:0] y;\n"
      "  constraint k { x == 0; x < y; }\n"
      "  constraint order { solve y before x; }\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    B o = new;\n"
      "    repeat (64) begin\n"
      "      if (o.randomize() && o.x == 0 && o.y > 0) held++;\n"
      "    end\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "64\n");
}

}  // namespace
