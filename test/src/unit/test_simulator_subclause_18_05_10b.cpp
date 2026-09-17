#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// 18.5.10: a constraint declared through a static prototype and a static
// external block is one static constraint, so the block turned off through
// one instance is off through another, and while it stands every draw of
// either instance holds x above 0, as the design
// test/src/e2e/static_constraint_blocks.sv runs it.
TEST(StaticConstraintBlocksRun, AStaticExternalBlockIsSharedAcrossInstances) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "  static constraint nonzero;\n"
      "endclass\n"
      "static constraint C::nonzero { x > 0; }\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    C c1 = new;\n"
      "    C c2 = new;\n"
      "    repeat (32) begin\n"
      "      void'(c1.randomize());\n"
      "      void'(c2.randomize());\n"
      "      if (c1.x > 0 && c2.x > 0) held++;\n"
      "    end\n"
      "    c1.nonzero.constraint_mode(0);\n"
      "    $display(\"%0d %0d\", held, c2.nonzero.constraint_mode());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 0\n");
}

// 18.5.10: a static block turned off through one instance is off for every
// instance's randomize(), so the other instance, whose draws all lay below
// 10 while the static bound stood, reaches 10 or more in some of 64 draws
// afterwards, while its own even, no static block, holds throughout.
TEST(StaticConstraintBlocksRun, AStaticBlockOffFreesEveryInstance) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "  static constraint bounded { x < 10; }\n"
      "  constraint even { x % 2 == 0; }\n"
      "endclass\n"
      "module t;\n"
      "  int below = 0, freed = 0, still_even = 0;\n"
      "  initial begin\n"
      "    C c1 = new;\n"
      "    C c2 = new;\n"
      "    repeat (32) begin\n"
      "      void'(c2.randomize());\n"
      "      if (c2.x < 10) below++;\n"
      "    end\n"
      "    c1.bounded.constraint_mode(0);\n"
      "    repeat (64) begin\n"
      "      void'(c2.randomize());\n"
      "      if (c2.x >= 10) freed = 1;\n"
      "      if (c2.x % 2 == 0) still_even++;\n"
      "    end\n"
      "    $display(\"%0d %0d %0d\", below, freed, still_even);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 1 64\n");
}

}  // namespace
