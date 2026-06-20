#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "common/types.h"
#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.14.2: in simulation an assumed property is checked like an asserted one —
// a true evaluation runs the pass statements, a false evaluation runs the fail
// statements, and a disabled evaluation runs neither.
TEST(AssumeStatement, ActionBlockChoiceFollowsPropertyOutcome) {
  EXPECT_EQ(SelectAssumeActionBlock(/*passed=*/true, /*disabled=*/false),
            AssertActionBlockChoice::kPass);
  EXPECT_EQ(SelectAssumeActionBlock(/*passed=*/false, /*disabled=*/false),
            AssertActionBlockChoice::kFail);
  EXPECT_EQ(SelectAssumeActionBlock(/*passed=*/false, /*disabled=*/true),
            AssertActionBlockChoice::kNone);
}

// §16.14.2: a disabled assume evaluation runs neither the pass nor the fail
// statements, even when the property would otherwise be considered to pass.
TEST(AssumeStatement, DisabledEvaluationRunsNeitherBranch) {
  EXPECT_EQ(SelectAssumeActionBlock(/*passed=*/true, /*disabled=*/true),
            AssertActionBlockChoice::kNone);
}

// §16.14.2: with the else clause omitted, a failing assume calls $error by
// default, unless a §20.11 control has disabled the fail action.
TEST(AssumeStatement, DefaultErrorOnFailureUnlessSuppressed) {
  EXPECT_TRUE(AssumeCallsDefaultErrorOnFailure(/*property_failed=*/true,
                                               /*has_else_clause=*/false,
                                               /*fail_action_enabled=*/true));
  EXPECT_FALSE(AssumeCallsDefaultErrorOnFailure(/*property_failed=*/true,
                                                /*has_else_clause=*/false,
                                                /*fail_action_enabled=*/false));
}

// §16.14.2: a present else clause supplies the fail action, so the default
// $error is not used; and a passing assumption never takes the fail action.
TEST(AssumeStatement, NoDefaultErrorWithElseOrOnPass) {
  EXPECT_FALSE(AssumeCallsDefaultErrorOnFailure(/*property_failed=*/true,
                                                /*has_else_clause=*/true,
                                                /*fail_action_enabled=*/true));
  EXPECT_FALSE(AssumeCallsDefaultErrorOnFailure(/*property_failed=*/false,
                                                /*has_else_clause=*/false,
                                                /*fail_action_enabled=*/true));
}

// §16.14.2: the pass and fail statements of an assume can be controlled by the
// §20.11 action control tasks; a disabled branch is dropped, and an enabled
// branch is kept.
TEST(AssumeStatement, ActionControlSuppressesSelectedBranch) {
  EXPECT_EQ(ResolveAssumeActionUnderControl(AssertActionBlockChoice::kFail,
                                            /*pass_enabled=*/true,
                                            /*fail_enabled=*/false),
            AssertActionBlockChoice::kNone);
  EXPECT_EQ(ResolveAssumeActionUnderControl(AssertActionBlockChoice::kPass,
                                            /*pass_enabled=*/false,
                                            /*fail_enabled=*/true),
            AssertActionBlockChoice::kNone);
  EXPECT_EQ(ResolveAssumeActionUnderControl(AssertActionBlockChoice::kFail,
                                            /*pass_enabled=*/true,
                                            /*fail_enabled=*/true),
            AssertActionBlockChoice::kFail);
}

// §16.14.2: within an assert or cover statement a biased dist is equivalent to
// the inside operator and the weights are ignored; within an assume statement
// the weights take effect.
TEST(AssumeStatement, BiasingWeightsIgnoredInAssertAndCover) {
  EXPECT_TRUE(BiasingWeightsIgnored(BiasedAssertionDirective::kAssert));
  EXPECT_TRUE(BiasingWeightsIgnored(BiasedAssertionDirective::kCover));
  EXPECT_FALSE(BiasingWeightsIgnored(BiasedAssertionDirective::kAssume));

  EXPECT_TRUE(BiasedDistActsAsInside(BiasedAssertionDirective::kAssert));
  EXPECT_TRUE(BiasedDistActsAsInside(BiasedAssertionDirective::kCover));
  EXPECT_FALSE(BiasedDistActsAsInside(BiasedAssertionDirective::kAssume));
}

// §16.14.2: an assumed property holds the same with or without biasing — the
// legal value set is the distribution's membership set, independent of the
// weights.
TEST(AssumeStatement, AssumedPropertyHoldsSameWithOrWithoutBiasing) {
  std::vector<int64_t> members = {0, 1};
  EXPECT_TRUE(
      AssumeValueIsLegalUnderBiasing(0, members, /*weights_present=*/true));
  EXPECT_TRUE(
      AssumeValueIsLegalUnderBiasing(0, members, /*weights_present=*/false));
  EXPECT_TRUE(
      AssumeValueIsLegalUnderBiasing(1, members, /*weights_present=*/true));
  EXPECT_FALSE(
      AssumeValueIsLegalUnderBiasing(2, members, /*weights_present=*/true));
}

// §16.14.2: in an assume statement the biasing weights select among the legal
// free-variable values according to the cumulative distribution. The weights
// 40:60 over candidates {0, 1} mirror the a1 example on page 478.
TEST(AssumeStatement, BiasingSelectsFreeVariableByWeight) {
  std::vector<uint32_t> weights = {40, 60};
  EXPECT_EQ(SelectBiasedFreeVariable(weights, 0u), static_cast<std::size_t>(0));
  EXPECT_EQ(SelectBiasedFreeVariable(weights, 39u),
            static_cast<std::size_t>(0));
  EXPECT_EQ(SelectBiasedFreeVariable(weights, 40u),
            static_cast<std::size_t>(1));
  EXPECT_EQ(SelectBiasedFreeVariable(weights, 99u),
            static_cast<std::size_t>(1));
}

// §16.14.2: a disabled assume evaluation runs neither branch, so the §20.11
// action control tasks cannot bring back a suppressed branch — a kNone choice
// stays kNone whatever the pass/fail enables are.
TEST(AssumeStatement, ActionControlDoesNotResurrectDisabledBranch) {
  EXPECT_EQ(ResolveAssumeActionUnderControl(AssertActionBlockChoice::kNone,
                                            /*pass_enabled=*/true,
                                            /*fail_enabled=*/true),
            AssertActionBlockChoice::kNone);
}

// §16.14.2: an assumed property holds only for the membership set of its
// distribution. With no legal values at all, every candidate is rejected,
// regardless of whether biasing weights are present.
TEST(AssumeStatement, NoLegalValuesRejectsEveryCandidate) {
  std::vector<int64_t> empty_members;
  EXPECT_FALSE(AssumeValueIsLegalUnderBiasing(0, empty_members,
                                              /*weights_present=*/true));
  EXPECT_FALSE(AssumeValueIsLegalUnderBiasing(0, empty_members,
                                              /*weights_present=*/false));
}

// §16.14.2: the weighted free-variable selection must stay well defined at the
// boundaries — an empty weight set has nothing to choose (index 0), a single
// candidate is always chosen, and a draw at or beyond the cumulative sum clamps
// to the last candidate rather than running off the end.
TEST(AssumeStatement, BiasingSelectionHandlesBoundaryInputs) {
  std::vector<uint32_t> none;
  EXPECT_EQ(SelectBiasedFreeVariable(none, 0u), static_cast<std::size_t>(0));

  std::vector<uint32_t> single = {7};
  EXPECT_EQ(SelectBiasedFreeVariable(single, 0u), static_cast<std::size_t>(0));
  EXPECT_EQ(SelectBiasedFreeVariable(single, 6u), static_cast<std::size_t>(0));

  std::vector<uint32_t> weights = {40, 60};
  EXPECT_EQ(SelectBiasedFreeVariable(weights, 100u),
            static_cast<std::size_t>(1));
  EXPECT_EQ(SelectBiasedFreeVariable(weights, 1000u),
            static_cast<std::size_t>(1));
}

}  // namespace
