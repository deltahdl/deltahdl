#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string MulticlockPropertySource(const std::string& items) {
  return "module t;\n"
         "  logic clk0 = 0;\n"
         "  logic clk1 = 0;\n"
         "  logic clk2 = 0;\n"
         "  int tick = 1;\n"
         "  logic sig0, sig1, b, s1, s2;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  int pass_sum = 0;\n"
         "  always #5 clk0 = ~clk0;\n"
         "  always #10 tick = tick + 1;\n"
         "  initial begin\n"
         "    #12 clk1 = 1; #8 clk1 = 0; #7 clk1 = 1; #8 clk1 = 0;\n"
         "    #10 clk1 = 1; #5 clk1 = 0; #7 clk1 = 1; #8 clk1 = 0;\n"
         "    #7 clk1 = 1; #6 clk1 = 0;\n"
         "  end\n"
         "  initial begin\n"
         "    #8 clk2 = 1; #8 clk2 = 0; #9 clk2 = 1; #7 clk2 = 0;\n"
         "    #6 clk2 = 1; #8 clk2 = 0; #9 clk2 = 1; #7 clk2 = 0;\n"
         "    #8 clk2 = 1; #4 clk2 = 0; #4 clk2 = 1; #1 clk2 = 0;\n"
         "  end\n"
         "  assign sig0 = tick inside {1, 2, 5, 7};\n"
         "  assign sig1 = tick inside {3, 5};\n"
         "  assign b = tick inside {1, 3, 6};\n"
         "  assign s1 = tick inside {2, 3};\n"
         "  assign s2 = tick inside {4, 7};\n" +
         items +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

struct MulticlockPropertyCounts {
  uint64_t passes;
  uint64_t fails;
  uint64_t pass_sum;
};

MulticlockPropertyCounts CountsOfMulticlockProperty(const std::string& spec) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      MulticlockPropertySource("  p: assert property (@(posedge clk0) " + spec +
                               ") begin passes++; pass_sum += $time; end "
                               "else fails++;\n"),
      f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull, ~0ull};
  Variable* fails = f.ctx.FindVariable("fails");
  Variable* pass_sum = f.ctx.FindVariable("pass_sum");
  return {passes->value.ToUint64(), fails->value.ToUint64(),
          pass_sum->value.ToUint64()};
}

TEST(MulticlockedProperty, AnAndOfClockedOperandsNeedsBothMatchesFromThePoint) {
  MulticlockPropertyCounts counts = CountsOfMulticlockProperty(
      "1 |-> (@(posedge clk0) sig0) and (@(posedge clk1) sig1)");
  EXPECT_EQ(counts.passes, 2u);
  EXPECT_EQ(counts.fails, 6u);
  EXPECT_EQ(counts.pass_sum, 72u);
}

TEST(MulticlockedProperty,
     NonoverlappingImplicationAwaitsTheNextTickOfTheConsequentClock) {
  MulticlockPropertyCounts counts =
      CountsOfMulticlockProperty("sig0 |=> @(posedge clk1) sig1");
  EXPECT_EQ(counts.passes, 5u);
  EXPECT_EQ(counts.fails, 3u);
  EXPECT_EQ(counts.pass_sum, 217u);
}

TEST(MulticlockedProperty,
     OverlappingImplicationChecksAtACoincidentTickAtOnce) {
  MulticlockPropertyCounts counts =
      CountsOfMulticlockProperty("sig0 |-> @(posedge clk1) sig1");
  EXPECT_EQ(counts.passes, 6u);
  EXPECT_EQ(counts.fails, 2u);
  EXPECT_EQ(counts.pass_sum, 262u);
}

TEST(MulticlockedProperty, IfElseReadsEachBranchAtItsClocksNearestTick) {
  MulticlockPropertyCounts counts = CountsOfMulticlockProperty(
      "if (b) @(posedge clk1) s1 else @(posedge clk2) s2");
  EXPECT_EQ(counts.passes, 4u);
  EXPECT_EQ(counts.fails, 4u);
  EXPECT_EQ(counts.pass_sum, 147u);
}

TEST(MulticlockedProperty, SequenceAsPropertyIsTrueIffMatch) {
  EXPECT_EQ(EvalMulticlockedSequenceAsProperty(true), PropertyResult::kPass);
  EXPECT_EQ(EvalMulticlockedSequenceAsProperty(false), PropertyResult::kFail);

  EXPECT_NE(EvalMulticlockedSequenceAsProperty(true), PropertyResult::kPending);
  EXPECT_NE(EvalMulticlockedSequenceAsProperty(false),
            PropertyResult::kPending);
}

TEST(MulticlockedProperty, BooleanAndRequiresBothOperandMatches) {
  EXPECT_EQ(EvalMulticlockedAnd(true, true), PropertyResult::kPass);
  EXPECT_EQ(EvalMulticlockedAnd(true, false), PropertyResult::kFail);
  EXPECT_EQ(EvalMulticlockedAnd(false, true), PropertyResult::kFail);
  EXPECT_EQ(EvalMulticlockedAnd(false, false), PropertyResult::kFail);
}

TEST(MulticlockedProperty, NonOverlappingAdvancesToStrictlyFutureTick) {
  const std::vector<uint64_t> kConsequentTicks = {10, 20, 30};
  EXPECT_EQ(MulticlockedConsequentEvalTick(20, kConsequentTicks, false), 30u);
  EXPECT_FALSE(
      MulticlockedImplicationChecksImmediately(20, kConsequentTicks, false));
}

TEST(MulticlockedProperty, NonOverlappingHasNoTickPastTheEnd) {
  const std::vector<uint64_t> kConsequentTicks = {10, 20};
  EXPECT_EQ(MulticlockedConsequentEvalTick(20, kConsequentTicks, false),
            kNoMulticlockTick);
}

TEST(MulticlockedProperty, OverlappingChecksImmediatelyOnCoincidentTick) {
  const std::vector<uint64_t> kConsequentTicks = {10, 20, 30};
  EXPECT_EQ(MulticlockedConsequentEvalTick(20, kConsequentTicks, true), 20u);
  EXPECT_TRUE(
      MulticlockedImplicationChecksImmediately(20, kConsequentTicks, true));
}

TEST(MulticlockedProperty, OverlappingWithoutCoincidentTickActsNonOverlapping) {
  const std::vector<uint64_t> kConsequentTicks = {10, 25, 30};
  EXPECT_EQ(MulticlockedConsequentEvalTick(20, kConsequentTicks, true), 25u);
  EXPECT_FALSE(
      MulticlockedImplicationChecksImmediately(20, kConsequentTicks, true));
}

TEST(MulticlockedProperty, ImplicationConsequentIsMulticlockedAnd) {
  const std::vector<uint64_t> kClk1Ticks = {15, 25};
  const uint64_t kEvalTick =
      MulticlockedConsequentEvalTick(10, kClk1Ticks, false);
  EXPECT_EQ(kEvalTick, 15u);

  EXPECT_EQ(EvalMulticlockedAnd(true, true), PropertyResult::kPass);
  EXPECT_EQ(EvalMulticlockedAnd(true, false), PropertyResult::kFail);
}

TEST(MulticlockedProperty, IfThenBranchAllowsOverlappingTick) {
  const std::vector<uint64_t> kThenTicks = {12, 18, 24};
  EXPECT_EQ(MulticlockedIfBranchEvalTick(12, kThenTicks), 12u);
}

TEST(MulticlockedProperty, IfElseBranchTakesNearestNonStrictlySubsequentTick) {
  const std::vector<uint64_t> kElseTicks = {10, 22, 33};
  EXPECT_EQ(MulticlockedIfBranchEvalTick(15, kElseTicks), 22u);
}

TEST(MulticlockedProperty, IfElseBranchAdmitsCoincidentTick) {
  const std::vector<uint64_t> kElseTicks = {15, 22, 33};
  EXPECT_EQ(MulticlockedIfBranchEvalTick(15, kElseTicks), 15u);
}

TEST(MulticlockedProperty, IfElseRoutesByCondition) {
  EXPECT_EQ(EvalPropertyIfElse(true, PropertyResult::kPass, true,
                               PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyIfElse(false, PropertyResult::kPass, true,
                               PropertyResult::kFail),
            PropertyResult::kFail);
}

TEST(MulticlockedProperty, NoClockTicksYieldsSentinel) {
  const std::vector<uint64_t> kNoTicks = {};
  EXPECT_EQ(NearestClockTickAtOrAfter(0, kNoTicks, true), kNoMulticlockTick);
  EXPECT_EQ(NearestClockTickAtOrAfter(0, kNoTicks, false), kNoMulticlockTick);
}

TEST(MulticlockedProperty, ConsequentTickWhenAntecedentEndsBeforeFirstTick) {
  const std::vector<uint64_t> kConsequentTicks = {10, 20};
  EXPECT_EQ(MulticlockedConsequentEvalTick(3, kConsequentTicks, false), 10u);
  EXPECT_EQ(MulticlockedConsequentEvalTick(3, kConsequentTicks, true), 10u);
  EXPECT_FALSE(
      MulticlockedImplicationChecksImmediately(3, kConsequentTicks, true));
}

TEST(MulticlockedProperty, OverlappingImplicationHasNoTickFromTheEnd) {
  const std::vector<uint64_t> kConsequentTicks = {5, 10};
  EXPECT_EQ(MulticlockedConsequentEvalTick(15, kConsequentTicks, true),
            kNoMulticlockTick);
  EXPECT_FALSE(
      MulticlockedImplicationChecksImmediately(15, kConsequentTicks, true));
}

TEST(MulticlockedProperty, IfBranchHasNoTickFromCondition) {
  const std::vector<uint64_t> kBranchTicks = {10, 20, 30};
  EXPECT_EQ(MulticlockedIfBranchEvalTick(40, kBranchTicks), kNoMulticlockTick);
}

}  // namespace
