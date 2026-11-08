#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

TEST(SatisfactionLevels, APropertyDecidedTrueHoldsStrongly) {
  LevelCounts counts = CountsOfLevel("start |-> ##1 b");
  EXPECT_EQ(counts.passes, 8u);
  EXPECT_EQ(counts.fails, 0u);
  EXPECT_EQ(counts.passes_at_end, 8u);
  EXPECT_EQ(counts.fails_at_end, 0u);
}

TEST(SatisfactionLevels, AWeakPropertyInFlightAtTheEndHolds) {
  LevelCounts counts = CountsOfLevel("start |-> always a");
  EXPECT_EQ(counts.passes, 7u);
  EXPECT_EQ(counts.fails, 0u);
  EXPECT_EQ(counts.passes_at_end, 8u);
  EXPECT_EQ(counts.fails_at_end, 0u);
}

TEST(SatisfactionLevels, AStrongPropertyInFlightAtTheEndIsPending) {
  LevelCounts counts = CountsOfLevel("start |-> s_eventually c");
  EXPECT_EQ(counts.passes, 7u);
  EXPECT_EQ(counts.fails, 0u);
  EXPECT_EQ(counts.passes_at_end, 7u);
  EXPECT_EQ(counts.fails_at_end, 1u);
}

TEST(SatisfactionLevels, APropertyThatSawABadStateFails) {
  LevelCounts counts = CountsOfLevel("start |-> ##1 c");
  EXPECT_EQ(counts.passes, 7u);
  EXPECT_EQ(counts.fails, 1u);
  EXPECT_EQ(counts.passes_at_end, 7u);
  EXPECT_EQ(counts.fails_at_end, 1u);
}

}  // namespace
