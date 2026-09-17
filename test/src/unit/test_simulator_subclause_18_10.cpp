#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A Channel whose constraints are modified through the four ways of the
// clause: an if-else and an implication predicated on a state fast, a cap
// block to be turned off, an order relating top to a base to be held, and
// a dist whose weights are the state variables w_one and w_two.
const char* const kChannel =
    "class Channel;\n"
    "  rand bit [7:0] len;\n"
    "  rand int sel;\n"
    "  rand int base, top;\n"
    "  int fast = 0;\n"
    "  int w_one = 1, w_two = 1;\n"
    "  constraint speed { if (fast) len < 16; else len >= 16; }\n"
    "  constraint floor { fast -> len > 3; }\n"
    "  constraint cap { len < 200; }\n"
    "  constraint pick { sel dist { 1 := w_one, 2 := w_two }; }\n"
    "  constraint order { top > base; top < base + 8; }\n"
    "endclass\n"
    "module t;\n";

// 18.10: implication and if-else constraints are predicated on a state
// variable, so changing fast between calls changes what randomize() solves:
// with it set len lies in (3, 16) on every draw, with it clear at or above
// 16, as the design test/src/e2e/dynamic_constraint_modification.sv runs it.
TEST(DynamicConstraintModificationRun, AStateVariablePredicatesTheBlocks) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kChannel) +
                     "  int short_draws = 0, long_draws = 0;\n"
                     "  initial begin\n"
                     "    Channel c = new;\n"
                     "    c.fast = 1;\n"
                     "    repeat (32) begin\n"
                     "      void'(c.randomize());\n"
                     "      if (c.len > 3 && c.len < 16) short_draws++;\n"
                     "    end\n"
                     "    c.fast = 0;\n"
                     "    repeat (32) begin\n"
                     "      void'(c.randomize());\n"
                     "      if (c.len >= 16) long_draws++;\n"
                     "    end\n"
                     "    $display(\"%0d %0d\", short_draws, long_draws);\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "32 32\n");
}

// 18.10: a block made inactive through constraint_mode() is ignored by
// randomize() and a variable made inactive through rand_mode() is a state
// variable to the solver: with cap off len reaches 200 in some of 64 draws
// and with it back on in none, and base held at 1000 leaves top drawn in
// (1000, 1008) on every call.
TEST(DynamicConstraintModificationRun, TheModeCallsChangeWhatIsSolved) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kChannel) +
          "  int high_off = 0, high_on = 0, near = 0;\n"
          "  initial begin\n"
          "    Channel c = new;\n"
          "    c.cap.constraint_mode(0);\n"
          "    repeat (64) begin\n"
          "      void'(c.randomize());\n"
          "      if (c.len >= 200) high_off++;\n"
          "    end\n"
          "    c.cap.constraint_mode(1);\n"
          "    repeat (64) begin\n"
          "      void'(c.randomize());\n"
          "      if (c.len >= 200) high_on++;\n"
          "    end\n"
          "    c.base = 1000;\n"
          "    c.base.rand_mode(0);\n"
          "    repeat (32) begin\n"
          "      void'(c.randomize());\n"
          "      if (c.base == 1000 && c.top > 1000 && c.top < 1008) near++;\n"
          "    end\n"
          "    $display(\"%0d %0d %0d\", high_off > 0, high_on, near);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0 32\n");
}

// 18.10: the weights of a dist can be changed, moving the probability of
// each value: read from state variables at each call, 9:1 draws more ones
// than twos over 64 calls and 1:9 more twos than ones, every draw one of
// the two.
TEST(DynamicConstraintModificationRun, ChangedWeightsMoveTheDistribution) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kChannel) +
          "  int ones = 0, twos = 0, first, second, all_named = 1;\n"
          "  initial begin\n"
          "    Channel c = new;\n"
          "    c.w_one = 9;\n"
          "    c.w_two = 1;\n"
          "    repeat (64) begin\n"
          "      void'(c.randomize());\n"
          "      if (c.sel == 1) ones++; else if (c.sel == 2) twos++;\n"
          "      else all_named = 0;\n"
          "    end\n"
          "    first = ones > twos;\n"
          "    ones = 0;\n"
          "    twos = 0;\n"
          "    c.w_one = 1;\n"
          "    c.w_two = 9;\n"
          "    repeat (64) begin\n"
          "      void'(c.randomize());\n"
          "      if (c.sel == 1) ones++; else if (c.sel == 2) twos++;\n"
          "      else all_named = 0;\n"
          "    end\n"
          "    second = twos > ones;\n"
          "    $display(\"%0d %0d %0d\", first, second, all_named);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1\n");
}

}  // namespace
