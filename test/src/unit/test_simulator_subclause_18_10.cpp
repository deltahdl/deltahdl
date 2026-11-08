#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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

TEST(DynamicConstraintModificationRun, AStateVariablePredicatesTheBlocks) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kChannel) +
                     "  int short_draws = 0, long_draws = 0;\n"
                     "  initial begin\n"
                     "    static Channel c = new;\n"
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

TEST(DynamicConstraintModificationRun, TheModeCallsChangeWhatIsSolved) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kChannel) +
          "  int high_off = 0, high_on = 0, near = 0;\n"
          "  initial begin\n"
          "    static Channel c = new;\n"
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

TEST(DynamicConstraintModificationRun, ChangedWeightsMoveTheDistribution) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kChannel) +
          "  int ones = 0, twos = 0, first, second, all_named = 1;\n"
          "  initial begin\n"
          "    static Channel c = new;\n"
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
