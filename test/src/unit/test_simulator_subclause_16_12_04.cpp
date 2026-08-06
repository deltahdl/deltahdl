#include <gtest/gtest.h>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.12.4: a disjunction property holds if, and only if, at least one of its
// two operand property expressions holds. Two passing operands plainly hold.
TEST(PropertyDisjunction, BothOperandsPass) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);
}

// §16.12.4: one holding operand is enough, so a passing left operand carries
// the disjunction even when the right operand fails.
TEST(PropertyDisjunction, LeftOperandPasses) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kPass);
}

// §16.12.4: symmetric to the previous case — a passing right operand alone
// makes the disjunction hold.
TEST(PropertyDisjunction, RightOperandPasses) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kPass);
}

// §16.12.4: only when neither operand holds does the disjunction fail.
TEST(PropertyDisjunction, BothOperandsFail) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kFail);
}

// A vacuous pass counts as the operand holding, so it satisfies the
// "at least one holds" condition on its own.
TEST(PropertyDisjunction, VacuousLeftStillHolds) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kVacuousPass, PropertyResult::kFail),
            PropertyResult::kPass);
}

TEST(PropertyDisjunction, VacuousRightStillHolds) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kVacuousPass),
            PropertyResult::kPass);
}

}  // namespace
