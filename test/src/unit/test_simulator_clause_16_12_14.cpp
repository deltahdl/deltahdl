#include <gtest/gtest.h>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.12.14: for an accept abort (accept_on / sync_accept_on) the overall
// evaluation is true when the abort condition becomes true; otherwise it equals
// the underlying property_expr's verdict. The true-condition case also shows
// the abort taking precedence over a contrary settled verdict (here kFail).
TEST(SvaEngineAbort, AcceptForcesTrueOnConditionElseInner) {
  EXPECT_EQ(EvalAbortAccept(/*abort_condition=*/true, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalAbortAccept(/*abort_condition=*/false, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalAbortAccept(/*abort_condition=*/false, PropertyResult::kPass),
            PropertyResult::kPass);
}

// §16.12.14: for a reject abort (reject_on / sync_reject_on) the overall
// evaluation is false when the abort condition becomes true; otherwise it
// equals the underlying property_expr's verdict. The true-condition case also
// shows the abort taking precedence over a contrary settled verdict (here
// kPass).
TEST(SvaEngineAbort, RejectForcesFalseOnConditionElseInner) {
  EXPECT_EQ(EvalAbortReject(/*abort_condition=*/true, PropertyResult::kPass),
            PropertyResult::kFail);
  EXPECT_EQ(EvalAbortReject(/*abort_condition=*/false, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalAbortReject(/*abort_condition=*/false, PropertyResult::kFail),
            PropertyResult::kFail);
}

// §16.12.14: reject_on(c) p is the same as not(accept_on(c) not p). The reject
// helper agrees with that equivalence for the definite verdicts.
TEST(SvaEngineAbort, RejectIsDualOfAccept) {
  for (bool cond : {false, true}) {
    for (PropertyResult inner :
         {PropertyResult::kPass, PropertyResult::kFail}) {
      PropertyResult dual =
          EvalPropertyNot(EvalAbortAccept(cond, EvalPropertyNot(inner)));
      EXPECT_EQ(EvalAbortReject(cond, inner), dual);
    }
  }
}

// §16.12.14: nested abort operators are evaluated in lexical order with the
// outermost taking precedence. For `accept_on(a) reject_on(b) p1`, when a and b
// become true in the same time step p succeeds; when only the inner condition b
// is true p fails.
TEST(SvaEngineAbort, NestedOutermostOperatorTakesPrecedence) {
  // accept_on (outer, forces true) wrapping reject_on (inner, forces false).
  EXPECT_EQ(
      EvalNestedAbort(/*outer_forces_true=*/true, /*outer_condition=*/true,
                      /*inner_forces_true=*/false, /*inner_condition=*/true,
                      PropertyResult::kPass),
      PropertyResult::kPass);
  // Inner reject condition true, outer accept condition not yet true: p fails.
  EXPECT_EQ(
      EvalNestedAbort(/*outer_forces_true=*/true, /*outer_condition=*/false,
                      /*inner_forces_true=*/false, /*inner_condition=*/true,
                      PropertyResult::kPass),
      PropertyResult::kFail);
}

// §16.12.14: the abort condition is evaluated using sampled values as a regular
// Boolean expression, unlike disable iff, whose condition uses current values.
TEST(SvaEngineAbort, AbortConditionUsesSampledValuesUnlikeDisableIff) {
  EXPECT_TRUE(AbortConditionUsesSampledValues());
  // disable iff evaluates its condition with current values — the contrasting
  // rule §16.12.14 calls out for the abort condition.
  EXPECT_TRUE(DisableConditionUsesCurrentValues());
}

// §16.12.14: asynchronous abort operators are evaluated at every simulation
// time step; the synchronous operators are evaluated only when the clocking
// event happens.
TEST(SvaEngineAbort, SynchronousAbortEvaluatesOnlyAtClockingEvent) {
  EXPECT_FALSE(
      AbortConditionEvaluatedAtClockingEventOnly(/*synchronous_abort=*/false));
  EXPECT_TRUE(
      AbortConditionEvaluatedAtClockingEventOnly(/*synchronous_abort=*/true));
}

// §16.12.14 (edge case): when the abort condition does not become true the
// result equals the underlying property_expr's verdict exactly — including a
// vacuous pass, which is neither forced to a plain pass nor to a fail.
TEST(SvaEngineAbort, AbortPreservesVacuousInnerWhenConditionFalse) {
  EXPECT_EQ(
      EvalAbortAccept(/*abort_condition=*/false, PropertyResult::kVacuousPass),
      PropertyResult::kVacuousPass);
  EXPECT_EQ(
      EvalAbortReject(/*abort_condition=*/false, PropertyResult::kVacuousPass),
      PropertyResult::kVacuousPass);
}

// §16.12.14 (edge case): with neither nested abort condition true, both
// operators are quiet and the underlying property_expr verdict passes straight
// through, whatever it is.
TEST(SvaEngineAbort, NestedAbortWithNeitherConditionYieldsInnerProperty) {
  EXPECT_EQ(
      EvalNestedAbort(/*outer_forces_true=*/true, /*outer_condition=*/false,
                      /*inner_forces_true=*/false, /*inner_condition=*/false,
                      PropertyResult::kPass),
      PropertyResult::kPass);
  EXPECT_EQ(
      EvalNestedAbort(/*outer_forces_true=*/true, /*outer_condition=*/false,
                      /*inner_forces_true=*/false, /*inner_condition=*/false,
                      PropertyResult::kFail),
      PropertyResult::kFail);
}

// §16.12.14 (edge case): the outermost-precedence rule holds for the opposite
// polarity arrangement too. For `reject_on(a) accept_on(b) p1`, when both a and
// b fire the outer reject decides the verdict (fail); when only the inner
// accept fires it forces a pass even over a failing underlying property_expr.
TEST(SvaEngineAbort, NestedRejectOuterOverridesAcceptInner) {
  EXPECT_EQ(
      EvalNestedAbort(/*outer_forces_true=*/false, /*outer_condition=*/true,
                      /*inner_forces_true=*/true, /*inner_condition=*/true,
                      PropertyResult::kPass),
      PropertyResult::kFail);
  EXPECT_EQ(
      EvalNestedAbort(/*outer_forces_true=*/false, /*outer_condition=*/false,
                      /*inner_forces_true=*/true, /*inner_condition=*/true,
                      PropertyResult::kFail),
      PropertyResult::kPass);
}

}  // namespace
