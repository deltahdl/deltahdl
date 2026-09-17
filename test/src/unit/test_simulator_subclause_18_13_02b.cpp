#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// 18.13.2: the clause's three examples, $urandom_range(7, 0), (7) with
// minval omitted and (0, 7) with the arguments reversed, each yield a value
// from 0 to 7 inclusive: over 256 draws every draw of each form is within the
// range and every one of the eight values is drawn, as the design
// test/src/e2e/urandom_range_function.sv runs it.
TEST(UrandomRangeRun, TheThreeExamplesEachYieldZeroToSeven) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int i, within = 0;\n"
      "  int unsigned r;\n"
      "  bit [7:0] seen = 0, seen_omitted = 0, seen_reversed = 0;\n"
      "  initial begin\n"
      "    for (i = 0; i < 256; i++) begin\n"
      "      r = $urandom_range(7, 0); if (r <= 7) within++; seen[r] = 1;\n"
      "      r = $urandom_range(7); if (r <= 7) within++; seen_omitted[r] = "
      "1;\n"
      "      r = $urandom_range(0, 7); if (r <= 7) within++; seen_reversed[r] "
      "= 1;\n"
      "    end\n"
      "    $display(\"%0d %0d %0d %0d\", within, $countones(seen),\n"
      "             $countones(seen_omitted), $countones(seen_reversed));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "768 8 8 8\n");
}

// 18.13.2: the result and both arguments are unsigned, and the range is
// maxval ... minval inclusive: equal bounds of 5 return 5 on all of 32 draws,
// and bounds above the largest int, 32'hFFFF_FFF0 to 32'hFFFF_FFFF, keep
// every one of 32 draws at or above the lower bound, which a signed reading
// of either would not.
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

// 18.13.2: $urandom_range is automatically thread stable (18.14.2), so a
// forked thread seeded with 9 draws the same eight values whether the thread
// forked beside it draws eight numbers or a hundred and eight.
TEST(UrandomRangeRun, ASeededThreadReplaysBesideABusierNeighbour) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int i, k, stable = 0;\n"
      "  int unsigned a[8], c[8], other;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        process p = process::self();\n"
      "        p.srandom(9);\n"
      "        for (k = 0; k < 8; k++) a[k] = $urandom_range(1000);\n"
      "      end\n"
      "      repeat (8) other = $urandom_range(1000);\n"
      "    join\n"
      "    fork\n"
      "      begin\n"
      "        process q = process::self();\n"
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

}  // namespace
