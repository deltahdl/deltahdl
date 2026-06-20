#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

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
