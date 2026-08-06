#include <gtest/gtest.h>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.12.13: a strong eventually (`s_eventually`) holds when the inner
// property_expr holds at some current or future clock tick within the range.
TEST(SvaEngineEventually, StrongHoldsWithWitness) {
  EXPECT_EQ(EvalEventually(/*strong=*/true, /*inner_holds_within_range=*/true,
                           /*all_range_ticks_present=*/true),
            PropertyResult::kPass);
}

// §16.12.13: a strong eventually fails when no current or future clock tick in
// the range satisfies the inner property_expr — even when the range's later
// ticks are not yet present, as for the unbounded `s_eventually [2:$]` form.
TEST(SvaEngineEventually, StrongFailsWithoutWitness) {
  EXPECT_EQ(EvalEventually(/*strong=*/true, /*inner_holds_within_range=*/false,
                           /*all_range_ticks_present=*/true),
            PropertyResult::kFail);
  EXPECT_EQ(EvalEventually(/*strong=*/true, /*inner_holds_within_range=*/false,
                           /*all_range_ticks_present=*/false),
            PropertyResult::kFail);
}

// §16.12.13: a weak `eventually` holds when the inner property_expr holds at
// some tick within the range, exactly as the strong form does.
TEST(SvaEngineEventually, WeakHoldsWithWitness) {
  EXPECT_EQ(EvalEventually(/*strong=*/false, /*inner_holds_within_range=*/true,
                           /*all_range_ticks_present=*/true),
            PropertyResult::kPass);
}

// §16.12.13: a weak eventually over a fully observed range fails when the inner
// property_expr held at none of the range's ticks.
TEST(SvaEngineEventually, WeakFailsWhenRangeFullyObservedWithoutWitness) {
  EXPECT_EQ(EvalEventually(/*strong=*/false, /*inner_holds_within_range=*/false,
                           /*all_range_ticks_present=*/true),
            PropertyResult::kFail);
}

// §16.12.13: a weak eventually also holds when not all clock ticks within the
// range exist, because the weak form does not require those later ticks to be
// present.
TEST(SvaEngineEventually, WeakHoldsWhenRangeTicksMissing) {
  EXPECT_EQ(EvalEventually(/*strong=*/false, /*inner_holds_within_range=*/false,
                           /*all_range_ticks_present=*/false),
            PropertyResult::kPass);
}

// §16.12.13: a weak eventually with a witness passes even when the range's
// later ticks are not all present — the satisfying tick is reached before any
// missing tick matters, so incomplete observation of the range does not change
// the pass.
TEST(SvaEngineEventually, WeakHoldsWithWitnessWhenRangeTicksMissing) {
  EXPECT_EQ(EvalEventually(/*strong=*/false, /*inner_holds_within_range=*/true,
                           /*all_range_ticks_present=*/false),
            PropertyResult::kPass);
}

// §16.12.13: the non-ranged `s_eventually` covers every current or future clock
// tick (equivalent to strong(##[*0:$] property_expr)), so a witness makes it
// pass even when later clock ticks are not all present.
TEST(SvaEngineEventually, NonRangedStrongTakesWitness) {
  EXPECT_EQ(EvalEventually(/*strong=*/true, /*inner_holds_within_range=*/true,
                           /*all_range_ticks_present=*/false),
            PropertyResult::kPass);
}

}  // namespace
