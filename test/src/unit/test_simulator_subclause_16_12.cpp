#include <gtest/gtest.h>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.12: the result of property evaluation is either true or false. When
// an implication evaluation completes, EvalImplication returns one of the
// boolean outcomes (kPass / kFail) — never the not-yet-determined kPending.
TEST(PropertyEvaluation, PropertyEvaluationResultIsBoolean) {
  auto pass = EvalImplication(true, true, false);
  auto fail = EvalImplication(true, false, false);
  EXPECT_EQ(pass, PropertyResult::kPass);
  EXPECT_EQ(fail, PropertyResult::kFail);
  EXPECT_NE(pass, PropertyResult::kPending);
  EXPECT_NE(fail, PropertyResult::kPending);
}

// §16.12: a vacuous outcome still resolves to true; the rule is that an
// evaluation that completes yields a boolean.
TEST(PropertyEvaluation, VacuousResolvesToTrue) {
  auto v = EvalImplication(false, false, false);
  EXPECT_EQ(v, PropertyResult::kVacuousPass);
}

// §16.12: a disable iff that fires preempts evaluation; per the LRM this
// resolves as not-failed (modeled here as a vacuous pass), matching the
// "true or false" boundary at evaluation end.
TEST(PropertyEvaluation, DisableIffPreemptsToVacuousPass) {
  auto inner = EvalImplication(true, false, false);
  EXPECT_EQ(inner, PropertyResult::kFail);
  auto preempted = EvalWithDisableIff(true, inner);
  EXPECT_EQ(preempted, PropertyResult::kVacuousPass);
}

}  // namespace
