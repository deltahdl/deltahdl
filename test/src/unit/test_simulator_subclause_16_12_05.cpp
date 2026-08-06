#include <gtest/gtest.h>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.12.5: a conjunction property holds if, and only if, both operand
// property expressions hold. Pass conjoined with pass yields pass.
TEST(PropertyConjunction, BothOperandsPass) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);
}

// A vacuous pass still counts as the operand holding, so conjoining it with
// a pass keeps the conjunction holding.
TEST(PropertyConjunction, VacuousOperandStillHolds) {
  EXPECT_EQ(
      EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kVacuousPass),
      PropertyResult::kPass);
}

// §16.12.5: if either operand fails the conjunction fails, regardless of
// which side carries the failure.
TEST(PropertyConjunction, LeftOperandFails) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kFail);
}

TEST(PropertyConjunction, RightOperandFails) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kFail);
}

// Edge case: when neither operand holds the conjunction still fails.
TEST(PropertyConjunction, BothOperandsFail) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kFail);
}

// Edge case: two vacuous passes both count as holding, so the conjunction
// holds vacuously rather than failing.
TEST(PropertyConjunction, BothOperandsVacuous) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kVacuousPass,
                            PropertyResult::kVacuousPass),
            PropertyResult::kPass);
}

// Edge case: a failure on one side dominates a vacuous hold on the other.
// The vacuous operand counts as holding, but the conjunction still needs both
// sides to hold, so the failing side forces an overall failure.
TEST(PropertyConjunction, FailDominatesVacuousLeft) {
  EXPECT_EQ(
      EvalPropertyAnd(PropertyResult::kFail, PropertyResult::kVacuousPass),
      PropertyResult::kFail);
}

TEST(PropertyConjunction, FailDominatesVacuousRight) {
  EXPECT_EQ(
      EvalPropertyAnd(PropertyResult::kVacuousPass, PropertyResult::kFail),
      PropertyResult::kFail);
}

// A vacuous hold conjoined with a genuine pass still holds, mirroring the
// pass-with-vacuous case from the other operand order.
TEST(PropertyConjunction, VacuousWithPassHolds) {
  EXPECT_EQ(
      EvalPropertyAnd(PropertyResult::kVacuousPass, PropertyResult::kPass),
      PropertyResult::kPass);
}

}  // namespace
