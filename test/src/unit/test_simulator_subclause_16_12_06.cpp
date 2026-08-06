#include <gtest/gtest.h>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.12.6: in the single-branch form `if (cond) p`, when the guard holds the
// property result is exactly that of the then-branch.
TEST(PropertyIfElse, SingleBranchGuardTrueTakesThen) {
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/true, PropertyResult::kPass,
                               /*has_else=*/false, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/true, PropertyResult::kFail,
                               /*has_else=*/false, PropertyResult::kPass),
            PropertyResult::kFail);
}

// §16.12.6: the first form is true if the guard is false, regardless of the
// then-branch. With no else there is nothing to check, so it holds vacuously.
TEST(PropertyIfElse, SingleBranchGuardFalseHoldsVacuously) {
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/false, PropertyResult::kFail,
                               /*has_else=*/false, PropertyResult::kPass),
            PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/false, PropertyResult::kPass,
                               /*has_else=*/false, PropertyResult::kPass),
            PropertyResult::kVacuousPass);
}

// §16.12.6: in the two-branch form `if (cond) p1 else p2`, a true guard makes
// the result that of property_expr1.
TEST(PropertyIfElse, TwoBranchGuardTrueTakesThen) {
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/true, PropertyResult::kPass,
                               /*has_else=*/true, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/true, PropertyResult::kFail,
                               /*has_else=*/true, PropertyResult::kPass),
            PropertyResult::kFail);
}

// §16.12.6: in the two-branch form a false guard routes evaluation to the
// else-branch, so the result is that of property_expr2.
TEST(PropertyIfElse, TwoBranchGuardFalseTakesElse) {
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/false, PropertyResult::kFail,
                               /*has_else=*/true, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/false, PropertyResult::kPass,
                               /*has_else=*/true, PropertyResult::kFail),
            PropertyResult::kFail);
}

// §16.12.6 edge case: the result is exactly the selected branch's result, so a
// vacuous hold in the chosen branch is carried through unchanged rather than
// being normalized to a plain pass.
TEST(PropertyIfElse, SelectedBranchVacuousResultPropagates) {
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/true, PropertyResult::kVacuousPass,
                               /*has_else=*/true, PropertyResult::kFail),
            PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/false, PropertyResult::kFail,
                               /*has_else=*/true, PropertyResult::kVacuousPass),
            PropertyResult::kVacuousPass);
}

// §16.12.6 edge case: an as-yet unresolved (pending) result in the chosen
// branch is likewise carried through, since the if-else result tracks the
// selected branch and defers along with it.
TEST(PropertyIfElse, SelectedBranchPendingResultPropagates) {
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/true, PropertyResult::kPending,
                               /*has_else=*/true, PropertyResult::kPass),
            PropertyResult::kPending);
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/false, PropertyResult::kPass,
                               /*has_else=*/true, PropertyResult::kPending),
            PropertyResult::kPending);
}

}  // namespace
