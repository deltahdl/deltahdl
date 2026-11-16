#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(UrandomRangeRun, TheThreeExamplesEachYieldZeroToSeven) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int i, in_range = 0;\n"
      "  int unsigned r;\n"
      "  bit [7:0] seen = 0, seen_omitted = 0, seen_reversed = 0;\n"
      "  initial begin\n"
      "    for (i = 0; i < 256; i++) begin\n"
      "      r = $urandom_range(7, 0); if (r <= 7) in_range++; seen[r] = 1;\n"
      "      r = $urandom_range(7); if (r <= 7) in_range++; seen_omitted[r] = "
      "1;\n"
      "      r = $urandom_range(0, 7); if (r <= 7) in_range++; "
      "seen_reversed[r] "
      "= 1;\n"
      "    end\n"
      "    $display(\"%0d %0d %0d %0d\", in_range, $countones(seen),\n"
      "             $countones(seen_omitted), $countones(seen_reversed));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "768 8 8 8\n");
}

TEST(UrandomRangeRun, EqualBoundsAndBoundsAboveTheLargestIntAreKept) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int i, equal_bounds = 0, above = 0;\n"
      "  int unsigned r;\n"
      "  initial begin\n"
      "    for (i = 0; i < 32; i++) begin\n"
      "      if ($urandom_range(5, 5) == 5) equal_bounds++;\n"
      "      r = $urandom_range(32'hFFFF_FFFF, 32'hFFFF_FFF0);\n"
      "      if (r >= 32'hFFFF_FFF0) above++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", equal_bounds, above);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32\n");
}

TEST(UrandomRangeRun, ASeededThreadReplaysBesideABusierNeighbour) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int i, k, stable = 0;\n"
      "  int unsigned a[8], c[8], other;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        automatic process p = process::self();\n"
      "        p.srandom(9);\n"
      "        for (k = 0; k < 8; k++) a[k] = $urandom_range(1000);\n"
      "      end\n"
      "      repeat (8) other = $urandom_range(1000);\n"
      "    join\n"
      "    fork\n"
      "      begin\n"
      "        automatic process q = process::self();\n"
      "        q.srandom(9);\n"
      "        for (k = 0; k < 8; k++) c[k] = $urandom_range(1000);\n"
      "      end\n"
      "      repeat (108) other = $urandom_range(1000);\n"
      "    join\n"
      "    for (i = 0; i < 8; i++) if (a[i] == c[i]) stable++;\n"
      "    $display(\"%0d\", stable);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8\n");
}

TEST(UrandomRangeRun, NegativeActualsConvertToIntUnsigned) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int i, kept = 0, inside_band = 0;\n"
      "  int unsigned r;\n"
      "  initial begin\n"
      "    for (i = 0; i < 32; i++) begin\n"
      "      if ($urandom_range(-1, -1) == 32'hFFFF_FFFF) kept++;\n"
      "      r = $urandom_range(-2, -3);\n"
      "      if (r == 32'hFFFF_FFFD || r == 32'hFFFF_FFFE) inside_band++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", kept, inside_band);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32\n");
}

TEST(UrandomRangeRun, ActualsWiderThanThirtyTwoBitsAreReduced) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int i, five = 0;\n"
      "  initial begin\n"
      "    for (i = 0; i < 32; i++)\n"
      "      if ($urandom_range(64'h1_0000_0005, 64'h2_0000_0005) == 5) "
      "five++;\n"
      "    $display(\"%0d\", five);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32\n");
}

TEST(UrandomRangeRun, TheResultIsUnsignedAsAnOperandAndThroughATypeReference) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  longint w;\n"
      "  initial begin\n"
      "    w = $urandom_range(-1, -1);\n"
      "    $display(\"%0d %0d %0d\", w == 64'hFFFF_FFFF, $urandom_range(3, 3) "
      "> -1,\n"
      "             type($urandom_range(1))'(-1) > 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0 1\n");
}

}  // namespace
