#include <gtest/gtest.h>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.12.11: weak `always property_expr` holds when the inner property_expr
// held at every present clock tick and fails when it failed at one of them.
TEST(SvaEngine, WeakAlwaysTakesInnerVerdictOverPresentTicks) {
  EXPECT_EQ(EvalAlways(/*strong=*/false, /*all_covered_ticks_present=*/true,
                       /*inner_holds_at_present_ticks=*/true),
            PropertyResult::kPass);
  EXPECT_EQ(EvalAlways(/*strong=*/false, /*all_covered_ticks_present=*/true,
                       /*inner_holds_at_present_ticks=*/false),
            PropertyResult::kFail);
}

// §16.12.11: for a weak always it is not required that all clock ticks within
// the range exist, so missing covered ticks do not by themselves cause a
// failure.
TEST(SvaEngine, WeakAlwaysIgnoresMissingCoveredTicks) {
  EXPECT_EQ(EvalAlways(/*strong=*/false, /*all_covered_ticks_present=*/false,
                       /*inner_holds_at_present_ticks=*/true),
            PropertyResult::kPass);
}

// §16.12.11: strong `s_always` holds only when every covered tick exists and
// the inner property_expr held at each of them.
TEST(SvaEngine, StrongAlwaysRequiresPresentTicksAndInnerVerdict) {
  EXPECT_EQ(EvalAlways(/*strong=*/true, /*all_covered_ticks_present=*/true,
                       /*inner_holds_at_present_ticks=*/true),
            PropertyResult::kPass);
  EXPECT_EQ(EvalAlways(/*strong=*/true, /*all_covered_ticks_present=*/true,
                       /*inner_holds_at_present_ticks=*/false),
            PropertyResult::kFail);
}

// §16.12.11: strong always fails when a covered tick is missing — the dual of
// the weak form's pass in the same situation.
TEST(SvaEngine, StrongAlwaysFailsWhenCoveredTickMissing) {
  EXPECT_EQ(EvalAlways(/*strong=*/true, /*all_covered_ticks_present=*/false,
                       /*inner_holds_at_present_ticks=*/true),
            PropertyResult::kFail);
}

// §16.12.11: the non-ranged weak always covers every current or future tick,
// modelled as a minimum of 0 with an unbounded maximum, so every index from the
// current step onward is covered.
TEST(SvaEngine, NonRangedAlwaysCoversEveryFutureTick) {
  EXPECT_TRUE(
      AlwaysRangeCovers(/*index=*/0, /*range_min=*/0, kAlwaysUnboundedMax));
  EXPECT_TRUE(
      AlwaysRangeCovers(/*index=*/9, /*range_min=*/0, kAlwaysUnboundedMax));
}

// §16.12.11: a bounded range covers exactly the inclusive span of clock ticks
// it specifies; ticks before the minimum or after the maximum are not covered.
TEST(SvaEngine, BoundedRangeCoversInclusiveSpan) {
  EXPECT_FALSE(
      AlwaysRangeCovers(/*index=*/1, /*range_min=*/2, /*range_max=*/4));
  EXPECT_TRUE(AlwaysRangeCovers(/*index=*/2, /*range_min=*/2, /*range_max=*/4));
  EXPECT_TRUE(AlwaysRangeCovers(/*index=*/4, /*range_min=*/2, /*range_max=*/4));
  EXPECT_FALSE(
      AlwaysRangeCovers(/*index=*/5, /*range_min=*/2, /*range_max=*/4));
}

// §16.12.11: an unbounded weak range covers every tick from its minimum onward.
TEST(SvaEngine, UnboundedRangeCoversFromMinimumOnward) {
  EXPECT_FALSE(
      AlwaysRangeCovers(/*index=*/2, /*range_min=*/3, kAlwaysUnboundedMax));
  EXPECT_TRUE(
      AlwaysRangeCovers(/*index=*/3, /*range_min=*/3, kAlwaysUnboundedMax));
  EXPECT_TRUE(
      AlwaysRangeCovers(/*index=*/100, /*range_min=*/3, kAlwaysUnboundedMax));
}

// §16.12.11: for a strong always the covered ticks all exist when at least
// `range_max` further ticks are available, counting from the current step.
TEST(SvaEngine, StrongAlwaysTicksPresentWhenEnoughFutureTicks) {
  EXPECT_TRUE(
      AlwaysStrongTicksAllPresent(/*range_max=*/3, /*future_clock_ticks=*/3));
  EXPECT_TRUE(
      AlwaysStrongTicksAllPresent(/*range_max=*/3, /*future_clock_ticks=*/5));
  EXPECT_FALSE(
      AlwaysStrongTicksAllPresent(/*range_max=*/3, /*future_clock_ticks=*/2));
}

// §16.12.11: composing the helpers reproduces the strong-always semantics —
// when the range's ticks are not all present the property fails regardless of
// the inner verdict, and otherwise it takes the inner verdict.
TEST(SvaEngine, StrongAlwaysComposesPresenceWithInnerVerdict) {
  bool present =
      AlwaysStrongTicksAllPresent(/*range_max=*/4, /*future_clock_ticks=*/2);
  EXPECT_EQ(EvalAlways(/*strong=*/true, present,
                       /*inner_holds_at_present_ticks=*/true),
            PropertyResult::kFail);

  present =
      AlwaysStrongTicksAllPresent(/*range_max=*/4, /*future_clock_ticks=*/4);
  EXPECT_EQ(EvalAlways(/*strong=*/true, present,
                       /*inner_holds_at_present_ticks=*/true),
            PropertyResult::kPass);
}

}  // namespace
