#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The design of test/src/e2e/satisfaction_levels.sv around one assertion:
// clk rises at 5, 15, ..., 75 so that tick n is at 10n - 5, the run ending
// at 80; start is high at 1 alone, a throughout, b at 2 alone and c never.
std::string LevelsSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic start, a, b, c;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign start = tick inside {1};\n"
         "  assign a = 1;\n"
         "  assign b = tick inside {2};\n"
         "  assign c = 0;\n" +
         items +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

// The pass and fail counts of the assertion over `spec` at the ticks, and
// then with the attempts in flight at the end of the run decided, in the
// final blocks.
struct LevelCounts {
  uint64_t passes;
  uint64_t fails;
  uint64_t passes_at_end;
  uint64_t fails_at_end;
};

LevelCounts CountsOfLevel(const std::string& spec) {
  SimFixture f;
  auto* passes =
      RunAndFindVar(LevelsSource("  p: assert property (@(posedge clk) " +
                                 spec + ") passes++; else fails++;\n"),
                    f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull, ~0ull, ~0ull};
  Variable* fails = f.ctx.FindVariable("fails");
  LevelCounts counts{passes->value.ToUint64(), fails->value.ToUint64(), 0, 0};
  f.ctx.RunFinalBlocks();
  counts.passes_at_end = passes->value.ToUint64();
  counts.fails_at_end = fails->value.ToUint64();
  return counts;
}

// §16.12.21: a property holds strongly where no bad state has been seen,
// every obligation has been met and no extension of the path can fail it:
// start |-> ##1 b is decided true at 2, and every attempt before the end.
TEST(SatisfactionLevels, APropertyDecidedTrueHoldsStrongly) {
  LevelCounts counts = CountsOfLevel("start |-> ##1 b");
  EXPECT_EQ(counts.passes, 8u);
  EXPECT_EQ(counts.fails, 0u);
  EXPECT_EQ(counts.passes_at_end, 8u);
  EXPECT_EQ(counts.fails_at_end, 0u);
}

// §16.12.21: a property holds without holding strongly where no bad state
// has been seen and no obligation is unmet but an extension may fail it:
// start |-> always a, always being weak, is in flight when the run ends
// and holds there.
TEST(SatisfactionLevels, AWeakPropertyInFlightAtTheEndHolds) {
  LevelCounts counts = CountsOfLevel("start |-> always a");
  EXPECT_EQ(counts.passes, 7u);
  EXPECT_EQ(counts.fails, 0u);
  EXPECT_EQ(counts.passes_at_end, 8u);
  EXPECT_EQ(counts.fails_at_end, 0u);
}

// §16.12.21: a property is pending where no bad state has been seen but an
// obligation has not been met: start |-> s_eventually c, s_eventually
// being strong and c never happening, is in flight when the run ends,
// which reports its attempt as failing.
TEST(SatisfactionLevels, AStrongPropertyInFlightAtTheEndIsPending) {
  LevelCounts counts = CountsOfLevel("start |-> s_eventually c");
  EXPECT_EQ(counts.passes, 7u);
  EXPECT_EQ(counts.fails, 0u);
  EXPECT_EQ(counts.passes_at_end, 7u);
  EXPECT_EQ(counts.fails_at_end, 1u);
}

// §16.12.21: a property fails where a bad state has been seen, so that it
// holds on no extension: start |-> ##1 c sees c low at 2.
TEST(SatisfactionLevels, APropertyThatSawABadStateFails) {
  LevelCounts counts = CountsOfLevel("start |-> ##1 c");
  EXPECT_EQ(counts.passes, 7u);
  EXPECT_EQ(counts.fails, 1u);
  EXPECT_EQ(counts.passes_at_end, 7u);
  EXPECT_EQ(counts.fails_at_end, 1u);
}

}  // namespace
