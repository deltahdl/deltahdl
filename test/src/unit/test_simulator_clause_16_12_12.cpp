#include <gtest/gtest.h>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// Tests for LRM §16.12.12 "Until property", covering the four forms:
//   a until        b  (weak,   non-overlapping)
//   a s_until      b  (strong, non-overlapping)
//   a until_with   b  (weak,   overlapping)
//   a s_until_with b  (strong, overlapping)
//
// `UntilLeftHoldsRequired` models where the left operand must hold relative to
// the first tick at which the right operand holds (the overlapping vs
// non-overlapping axis); `EvalUntil` combines that with whether the right
// operand ever holds (the weak vs strong axis).

// §16.12.12: for the non-overlapping forms the left operand is required only on
// the ticks before the first tick where the right operand holds, so it need not
// hold at that tick itself.
TEST(SvaEngineUntil, NonOverlappingExcludesRhsTick) {
  // Right operand first holds at offset 2; left operand held at ticks 0 and 1.
  EXPECT_TRUE(
      UntilLeftHoldsRequired(/*overlapping=*/false, /*lhs_run_length=*/2,
                             /*first_rhs_index=*/2, /*trace_length=*/5));
  // Left operand stopped holding before the required window was covered.
  EXPECT_FALSE(
      UntilLeftHoldsRequired(/*overlapping=*/false, /*lhs_run_length=*/1,
                             /*first_rhs_index=*/2, /*trace_length=*/5));
}

// §16.12.12: for the overlapping forms the left operand is also required at the
// tick where the right operand first holds.
TEST(SvaEngineUntil, OverlappingIncludesRhsTick) {
  // The same trace that satisfies the non-overlapping form fails here because
  // the left operand must also hold at the right operand's tick (offset 2).
  EXPECT_FALSE(
      UntilLeftHoldsRequired(/*overlapping=*/true, /*lhs_run_length=*/2,
                             /*first_rhs_index=*/2, /*trace_length=*/5));
  EXPECT_TRUE(UntilLeftHoldsRequired(/*overlapping=*/true, /*lhs_run_length=*/3,
                                     /*first_rhs_index=*/2,
                                     /*trace_length=*/5));
}

// §16.12.12: when the right operand holds at the starting tick, the
// non-overlapping form does not require the left operand to hold there at all.
TEST(SvaEngineUntil, NonOverlappingRhsAtStartRequiresNothing) {
  EXPECT_TRUE(
      UntilLeftHoldsRequired(/*overlapping=*/false, /*lhs_run_length=*/0,
                             /*first_rhs_index=*/0, /*trace_length=*/4));
}

// §16.12.12: when the right operand holds at the starting tick, the overlapping
// form still requires the left operand to hold at that one (overlapping) tick.
TEST(SvaEngineUntil, OverlappingRhsAtStartRequiresLhsThere) {
  EXPECT_FALSE(
      UntilLeftHoldsRequired(/*overlapping=*/true, /*lhs_run_length=*/0,
                             /*first_rhs_index=*/0, /*trace_length=*/4));
  EXPECT_TRUE(UntilLeftHoldsRequired(/*overlapping=*/true, /*lhs_run_length=*/1,
                                     /*first_rhs_index=*/0,
                                     /*trace_length=*/4));
}

// §16.12.12: when the right operand never holds, the left operand is required
// at every tick of the trace for both windowings.
TEST(SvaEngineUntil, RhsNeverRequiresLhsEverywhere) {
  EXPECT_TRUE(UntilLeftHoldsRequired(/*overlapping=*/false,
                                     /*lhs_run_length=*/3, kUntilRhsNever,
                                     /*trace_length=*/3));
  EXPECT_TRUE(UntilLeftHoldsRequired(/*overlapping=*/true, /*lhs_run_length=*/3,
                                     kUntilRhsNever, /*trace_length=*/3));
  EXPECT_FALSE(UntilLeftHoldsRequired(/*overlapping=*/false,
                                      /*lhs_run_length=*/2, kUntilRhsNever,
                                      /*trace_length=*/3));
}

// §16.12.12: a weak until holds whenever the left operand held over its
// required window, regardless of whether the right operand ever holds.
TEST(SvaEngineUntil, WeakHoldsRegardlessOfRhsPresence) {
  EXPECT_EQ(EvalUntil(/*strong=*/false, /*rhs_holds_eventually=*/false,
                      /*lhs_holds_required=*/true),
            PropertyResult::kPass);
  EXPECT_EQ(EvalUntil(/*strong=*/false, /*rhs_holds_eventually=*/true,
                      /*lhs_holds_required=*/true),
            PropertyResult::kPass);
}

// §16.12.12: any until form fails when the left operand did not hold across its
// required window.
TEST(SvaEngineUntil, FailsWhenLeftOperandDidNotHold) {
  EXPECT_EQ(EvalUntil(/*strong=*/false, /*rhs_holds_eventually=*/true,
                      /*lhs_holds_required=*/false),
            PropertyResult::kFail);
  EXPECT_EQ(EvalUntil(/*strong=*/true, /*rhs_holds_eventually=*/true,
                      /*lhs_holds_required=*/false),
            PropertyResult::kFail);
}

// §16.12.12: a strong until requires a current or future tick at which the
// right operand holds; if none exists the property fails even though the same
// trace satisfies the corresponding weak form.
TEST(SvaEngineUntil, StrongRequiresRhsToHold) {
  EXPECT_EQ(EvalUntil(/*strong=*/true, /*rhs_holds_eventually=*/false,
                      /*lhs_holds_required=*/true),
            PropertyResult::kFail);
  EXPECT_EQ(EvalUntil(/*strong=*/true, /*rhs_holds_eventually=*/true,
                      /*lhs_holds_required=*/true),
            PropertyResult::kPass);
}

// §16.12.12: composing the helpers reproduces `a until b` (p1) — the left
// operand holds up to the first right-operand tick and the weak form holds even
// when the right operand only holds later.
TEST(SvaEngineUntil, ComposesWeakNonOverlapping) {
  bool lhs = UntilLeftHoldsRequired(/*overlapping=*/false, /*lhs_run_length=*/2,
                                    /*first_rhs_index=*/2, /*trace_length=*/5);
  EXPECT_EQ(EvalUntil(/*strong=*/false, /*rhs_holds_eventually=*/true, lhs),
            PropertyResult::kPass);
}

// §16.12.12: composing the helpers reproduces `a s_until b` (p2) failing when
// the right operand never holds, even though the left operand holds everywhere.
TEST(SvaEngineUntil, ComposesStrongNonOverlappingFailsWithoutRhs) {
  bool lhs = UntilLeftHoldsRequired(/*overlapping=*/false, /*lhs_run_length=*/3,
                                    kUntilRhsNever, /*trace_length=*/3);
  EXPECT_EQ(EvalUntil(/*strong=*/true, /*rhs_holds_eventually=*/false, lhs),
            PropertyResult::kFail);
}

// §16.12.12: composing the helpers reproduces `a s_until_with b` (p4) — the
// left operand holds through and including the right-operand tick and the right
// operand holds, so the strong overlapping form passes.
TEST(SvaEngineUntil, ComposesStrongOverlapping) {
  bool lhs = UntilLeftHoldsRequired(/*overlapping=*/true, /*lhs_run_length=*/3,
                                    /*first_rhs_index=*/2, /*trace_length=*/5);
  EXPECT_EQ(EvalUntil(/*strong=*/true, /*rhs_holds_eventually=*/true, lhs),
            PropertyResult::kPass);
}

// §16.12.12: composing the helpers reproduces `a until_with b` (p3) — the weak
// overlapping form requires the left operand through and including the
// right-operand tick but, being weak, does not require the right operand to
// hold at all. Here the left operand holds at every tick while the right
// operand never holds, so the property still passes.
TEST(SvaEngineUntil, ComposesWeakOverlapping) {
  bool lhs = UntilLeftHoldsRequired(/*overlapping=*/true, /*lhs_run_length=*/3,
                                    kUntilRhsNever, /*trace_length=*/3);
  EXPECT_EQ(EvalUntil(/*strong=*/false, /*rhs_holds_eventually=*/false, lhs),
            PropertyResult::kPass);
}

// §16.12.12: the weak overlapping form still enforces the left operand at the
// overlapping (right-operand) tick — when the left operand drops out exactly at
// that tick the property fails even though the right operand holds there.
TEST(SvaEngineUntil, ComposesWeakOverlappingFailsAtRhsTick) {
  bool lhs = UntilLeftHoldsRequired(/*overlapping=*/true, /*lhs_run_length=*/2,
                                    /*first_rhs_index=*/2, /*trace_length=*/5);
  EXPECT_EQ(EvalUntil(/*strong=*/false, /*rhs_holds_eventually=*/true, lhs),
            PropertyResult::kFail);
}

}  // namespace
