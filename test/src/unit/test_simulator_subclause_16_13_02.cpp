#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/sva_engine.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The design of test/src/e2e/multiclock_properties.sv around one
// assertion: clk0 rises at 5, 15, ..., 75 so that tick n of it is at 10n -
// 5, clk1 at 12, 27, 45, 57 and 72, its tick at 45 together with clk0's
// fifth, and clk2 at 8, 25, 38, 55, 70 and 78, its tick at 25 together
// with clk0's third; sig0 is high at 1, 2, 5 and 7, sig1 at 3 and 5, b at
// 1, 3 and 6, s1 at 2 and 3 and s2 at 4 and 7.
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

// The pass and fail counts of the assertion over `spec`, clocked on clk0,
// and the sum of the times of its passes, which tells the ticks apart.
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

// §16.13.2: the and of two clocked booleans holds at a point where both
// have matches beginning there, sig0 at the tick of clk0 and sig1 at the
// nearest tick of clk1, the coincident one at 45: the attempts from 15 and
// 45 hold, at 27 and 45, and the six others fail. The and is the
// consequent of 1 |->, since as the maximal property of the assertion it
// would have two semantic leading clocks, which §16.16 (e) forbids.
TEST(MulticlockedProperty, AnAndOfClockedOperandsNeedsBothMatchesFromThePoint) {
  MulticlockPropertyCounts counts = CountsOfMulticlockProperty(
      "1 |-> (@(posedge clk0) sig0) and (@(posedge clk1) sig1)");
  EXPECT_EQ(counts.passes, 2u);
  EXPECT_EQ(counts.fails, 6u);
  EXPECT_EQ(counts.pass_sum, 72u);
}

// §16.13.2: |=> advances from the end of each match of the antecedent to
// the nearest strictly subsequent tick of the consequent's clock, 57 for
// the attempt from 45 though clk1 ticks at 45: the attempt from 15 holds
// at 27, those from 5, 45 and 65 fail, and the four with sig0 low hold.
TEST(MulticlockedProperty,
     NonoverlappingImplicationAwaitsTheNextTickOfTheConsequentClock) {
  MulticlockPropertyCounts counts =
      CountsOfMulticlockProperty("sig0 |=> @(posedge clk1) sig1");
  EXPECT_EQ(counts.passes, 5u);
  EXPECT_EQ(counts.fails, 3u);
  EXPECT_EQ(counts.pass_sum, 217u);
}

// §16.13.2: |-> checks the consequent immediately where its clock ticks at
// the end of the antecedent, as at 45, and at the next tick of its clock
// otherwise: the attempt from 45 holds there too.
TEST(MulticlockedProperty,
     OverlappingImplicationChecksAtACoincidentTickAtOnce) {
  MulticlockPropertyCounts counts =
      CountsOfMulticlockProperty("sig0 |-> @(posedge clk1) sig1");
  EXPECT_EQ(counts.passes, 6u);
  EXPECT_EQ(counts.fails, 2u);
  EXPECT_EQ(counts.pass_sum, 262u);
}

// §16.13.2: if-else reads its condition at the property's clock and the
// branch chosen at the nearest, possibly overlapping, tick of the branch's
// clock: the attempts from 5, 25, 35 and 65 hold, at 12, 27, 38 and 70,
// and those from 15, 45, 55 and 75 fail.
TEST(MulticlockedProperty, IfElseReadsEachBranchAtItsClocksNearestTick) {
  MulticlockPropertyCounts counts = CountsOfMulticlockProperty(
      "if (b) @(posedge clk1) s1 else @(posedge clk2) s2");
  EXPECT_EQ(counts.passes, 4u);
  EXPECT_EQ(counts.fails, 4u);
  EXPECT_EQ(counts.pass_sum, 147u);
}

// §16.13.2: a multiclocked sequence evaluated as a property is true iff there
// is a match beginning at that point, and the verdict is always a definite true
// or false (never pending) — mirroring the singly clocked true/false result.
TEST(MulticlockedProperty, SequenceAsPropertyIsTrueIffMatch) {
  EXPECT_EQ(EvalMulticlockedSequenceAsProperty(true), PropertyResult::kPass);
  EXPECT_EQ(EvalMulticlockedSequenceAsProperty(false), PropertyResult::kFail);

  EXPECT_NE(EvalMulticlockedSequenceAsProperty(true), PropertyResult::kPending);
  EXPECT_NE(EvalMulticlockedSequenceAsProperty(false),
            PropertyResult::kPending);
}

// §16.13.2: `(@(posedge clk0) sig0) and (@(posedge clk1) sig1)` is a
// multiclocked property that holds iff both differently clocked operands have a
// match beginning at the point.
TEST(MulticlockedProperty, BooleanAndRequiresBothOperandMatches) {
  EXPECT_EQ(EvalMulticlockedAnd(true, true), PropertyResult::kPass);
  EXPECT_EQ(EvalMulticlockedAnd(true, false), PropertyResult::kFail);
  EXPECT_EQ(EvalMulticlockedAnd(false, true), PropertyResult::kFail);
  EXPECT_EQ(EvalMulticlockedAnd(false, false), PropertyResult::kFail);
}

// §16.13.2: the nonoverlapping implication (|=>) synchronizes the consequent to
// the nearest strictly future tick of the consequent's clock. A
// consequent-clock tick coincident with the antecedent end does not qualify.
TEST(MulticlockedProperty, NonOverlappingAdvancesToStrictlyFutureTick) {
  const std::vector<uint64_t> kConsequentTicks = {10, 20, 30};
  EXPECT_EQ(MulticlockedConsequentEvalTick(/*antecedent_end_time=*/20,
                                           kConsequentTicks,
                                           /*overlapping=*/false),
            30u);
  EXPECT_FALSE(MulticlockedImplicationChecksImmediately(
      /*antecedent_end_time=*/20, kConsequentTicks, /*overlapping=*/false));
}

// §16.13.2: when the consequent clock has no strictly future tick, the
// nonoverlapping implication has nowhere to evaluate the consequent.
TEST(MulticlockedProperty, NonOverlappingHasNoTickPastTheEnd) {
  const std::vector<uint64_t> kConsequentTicks = {10, 20};
  EXPECT_EQ(MulticlockedConsequentEvalTick(/*antecedent_end_time=*/20,
                                           kConsequentTicks,
                                           /*overlapping=*/false),
            kNoMulticlockTick);
}

// §16.13.2: the overlapping implication (|->) awaits the nearest
// consequent-clock tick. When that clock ticks at the antecedent end the
// consequent is checked there immediately.
TEST(MulticlockedProperty, OverlappingChecksImmediatelyOnCoincidentTick) {
  const std::vector<uint64_t> kConsequentTicks = {10, 20, 30};
  EXPECT_EQ(MulticlockedConsequentEvalTick(/*antecedent_end_time=*/20,
                                           kConsequentTicks,
                                           /*overlapping=*/true),
            20u);
  EXPECT_TRUE(MulticlockedImplicationChecksImmediately(
      /*antecedent_end_time=*/20, kConsequentTicks, /*overlapping=*/true));
}

// §16.13.2: when the consequent clock does not tick at the antecedent end, the
// overlapping implication behaves as the nonoverlapping one — it advances to
// the nearest strictly future tick and does not check immediately.
TEST(MulticlockedProperty, OverlappingWithoutCoincidentTickActsNonOverlapping) {
  const std::vector<uint64_t> kConsequentTicks = {10, 25, 30};
  EXPECT_EQ(MulticlockedConsequentEvalTick(/*antecedent_end_time=*/20,
                                           kConsequentTicks,
                                           /*overlapping=*/true),
            25u);
  EXPECT_FALSE(MulticlockedImplicationChecksImmediately(
      /*antecedent_end_time=*/20, kConsequentTicks, /*overlapping=*/true));
}

// §16.13.2: combination example `@(posedge clk0) s0 |=> (@(posedge clk1) s1)
// and
// (@(posedge clk2) s2)`. After the antecedent advances to the consequent clock,
// the Boolean `and` of the two differently clocked consequents must both match.
TEST(MulticlockedProperty, ImplicationConsequentIsMulticlockedAnd) {
  const std::vector<uint64_t> kClk1Ticks = {15, 25};
  const uint64_t kEvalTick = MulticlockedConsequentEvalTick(
      /*antecedent_end_time=*/10, kClk1Ticks, /*overlapping=*/false);
  EXPECT_EQ(kEvalTick, 15u);

  EXPECT_EQ(EvalMulticlockedAnd(/*left_operand_has_match=*/true,
                                /*right_operand_has_match=*/true),
            PropertyResult::kPass);
  EXPECT_EQ(EvalMulticlockedAnd(/*left_operand_has_match=*/true,
                                /*right_operand_has_match=*/false),
            PropertyResult::kFail);
}

// §16.13.2: in a multiclocked if / if-else the condition is checked at the
// property clock, and the then-branch is evaluated at the nearest, possibly
// overlapping tick of its clock — a tick coincident with the condition check
// qualifies.
TEST(MulticlockedProperty, IfThenBranchAllowsOverlappingTick) {
  const std::vector<uint64_t> kThenTicks = {12, 18, 24};
  EXPECT_EQ(MulticlockedIfBranchEvalTick(/*condition_time=*/12, kThenTicks),
            12u);
}

// §16.13.2: the else-branch is evaluated at the nearest non-strictly subsequent
// tick of its clock, which likewise admits a coincident tick and otherwise
// takes the next available one.
TEST(MulticlockedProperty, IfElseBranchTakesNearestNonStrictlySubsequentTick) {
  const std::vector<uint64_t> kElseTicks = {10, 22, 33};
  EXPECT_EQ(MulticlockedIfBranchEvalTick(/*condition_time=*/15, kElseTicks),
            22u);
}

// §16.13.2: the else-branch's "non-strictly subsequent" reading admits a
// branch-clock tick coincident with the condition check — just like the
// then-branch's "possibly overlapping" reading — so a clock tick landing
// exactly at the condition time locates the else-branch evaluation there rather
// than at the following tick.
TEST(MulticlockedProperty, IfElseBranchAdmitsCoincidentTick) {
  const std::vector<uint64_t> kElseTicks = {15, 22, 33};
  EXPECT_EQ(MulticlockedIfBranchEvalTick(/*condition_time=*/15, kElseTicks),
            15u);
}

// §16.13.2: with the branch tick located, the if / if-else verdict is routed by
// the condition through the ordinary §16.12.6 property if-else over the branch
// results.
TEST(MulticlockedProperty, IfElseRoutesByCondition) {
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/true,
                               /*then_result=*/PropertyResult::kPass,
                               /*has_else=*/true,
                               /*else_result=*/PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/false,
                               /*then_result=*/PropertyResult::kPass,
                               /*has_else=*/true,
                               /*else_result=*/PropertyResult::kFail),
            PropertyResult::kFail);
}

// §16.13.2 edge case: with no ticks of the relevant clock there is nowhere to
// locate a multiclocked operand, so the search yields the no-tick sentinel
// under both the inclusive and strictly-future readings.
TEST(MulticlockedProperty, NoClockTicksYieldsSentinel) {
  const std::vector<uint64_t> kNoTicks = {};
  EXPECT_EQ(NearestClockTickAtOrAfter(/*from=*/0, kNoTicks, /*inclusive=*/true),
            kNoMulticlockTick);
  EXPECT_EQ(
      NearestClockTickAtOrAfter(/*from=*/0, kNoTicks, /*inclusive=*/false),
      kNoMulticlockTick);
}

// §16.13.2 edge case: when the antecedent ends before the consequent clock's
// first tick, no tick coincides with the end, so both the nonoverlapping and
// the overlapping forms advance to that first tick and neither checks
// immediately.
TEST(MulticlockedProperty, ConsequentTickWhenAntecedentEndsBeforeFirstTick) {
  const std::vector<uint64_t> kConsequentTicks = {10, 20};
  EXPECT_EQ(MulticlockedConsequentEvalTick(/*antecedent_end_time=*/3,
                                           kConsequentTicks,
                                           /*overlapping=*/false),
            10u);
  EXPECT_EQ(MulticlockedConsequentEvalTick(/*antecedent_end_time=*/3,
                                           kConsequentTicks,
                                           /*overlapping=*/true),
            10u);
  EXPECT_FALSE(MulticlockedImplicationChecksImmediately(
      /*antecedent_end_time=*/3, kConsequentTicks, /*overlapping=*/true));
}

// §16.13.2 error case: when the antecedent ends after the consequent clock's
// last tick, even the overlapping form finds no tick at or after the end, so
// the consequent cannot be located and the implication never checks
// immediately.
TEST(MulticlockedProperty, OverlappingImplicationHasNoTickFromTheEnd) {
  const std::vector<uint64_t> kConsequentTicks = {5, 10};
  EXPECT_EQ(MulticlockedConsequentEvalTick(/*antecedent_end_time=*/15,
                                           kConsequentTicks,
                                           /*overlapping=*/true),
            kNoMulticlockTick);
  EXPECT_FALSE(MulticlockedImplicationChecksImmediately(
      /*antecedent_end_time=*/15, kConsequentTicks, /*overlapping=*/true));
}

// §16.13.2 error case: when the branch clock has no tick at or after the
// condition check, the if / if-else branch cannot be located.
TEST(MulticlockedProperty, IfBranchHasNoTickFromCondition) {
  const std::vector<uint64_t> kBranchTicks = {10, 20, 30};
  EXPECT_EQ(MulticlockedIfBranchEvalTick(/*condition_time=*/40, kBranchTicks),
            kNoMulticlockTick);
}

}  // namespace
