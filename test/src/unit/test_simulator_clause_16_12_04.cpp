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

// Two vacuous holds both count as holding, so the disjunction holds rather than
// failing.
TEST(PropertyDisjunction, BothVacuousHold) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kVacuousPass,
                           PropertyResult::kVacuousPass),
            PropertyResult::kPass);
}

// Edge case: "at least one holds" is satisfied as soon as a single operand
// holds, even while the other operand is still being evaluated. A holding left
// operand makes the disjunction hold without waiting on a pending right
// operand.
TEST(PropertyDisjunction, HoldingLeftWithPendingRightHolds) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kPass, PropertyResult::kPending),
            PropertyResult::kPass);
}

// Edge case: symmetric to the previous one — a holding right operand carries
// the disjunction even though the left operand has not yet resolved.
TEST(PropertyDisjunction, HoldingRightWithPendingLeftHolds) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kPending, PropertyResult::kPass),
            PropertyResult::kPass);
}

}  // namespace
