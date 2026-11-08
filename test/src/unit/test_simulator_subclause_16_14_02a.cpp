#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <vector>

#include "simulator/sva_engine_queues.h"

using namespace delta;

namespace {

TEST(AssumeStatement, ActionBlockChoiceFollowsPropertyOutcome) {
  EXPECT_EQ(SelectAssumeActionBlock(true, false),
            AssertActionBlockChoice::kPass);
  EXPECT_EQ(SelectAssumeActionBlock(false, false),
            AssertActionBlockChoice::kFail);
  EXPECT_EQ(SelectAssumeActionBlock(false, true),
            AssertActionBlockChoice::kNone);
}

TEST(AssumeStatement, DisabledEvaluationRunsNeitherBranch) {
  EXPECT_EQ(SelectAssumeActionBlock(true, true),
            AssertActionBlockChoice::kNone);
}

TEST(AssumeStatement, DefaultErrorOnFailureUnlessSuppressed) {
  EXPECT_TRUE(AssumeCallsDefaultErrorOnFailure(true, false, true));
  EXPECT_FALSE(AssumeCallsDefaultErrorOnFailure(true, false, false));
}

TEST(AssumeStatement, NoDefaultErrorWithElseOrOnPass) {
  EXPECT_FALSE(AssumeCallsDefaultErrorOnFailure(true, true, true));
  EXPECT_FALSE(AssumeCallsDefaultErrorOnFailure(false, false, true));
}

TEST(AssumeStatement, ActionControlSuppressesSelectedBranch) {
  EXPECT_EQ(ResolveAssumeActionUnderControl(AssertActionBlockChoice::kFail,
                                            true, false),
            AssertActionBlockChoice::kNone);
  EXPECT_EQ(ResolveAssumeActionUnderControl(AssertActionBlockChoice::kPass,
                                            false, true),
            AssertActionBlockChoice::kNone);
  EXPECT_EQ(ResolveAssumeActionUnderControl(AssertActionBlockChoice::kFail,
                                            true, true),
            AssertActionBlockChoice::kFail);
}

TEST(AssumeStatement, BiasingWeightsIgnoredInAssertAndCover) {
  EXPECT_TRUE(BiasingWeightsIgnored(BiasedAssertionDirective::kAssert));
  EXPECT_TRUE(BiasingWeightsIgnored(BiasedAssertionDirective::kCover));
  EXPECT_FALSE(BiasingWeightsIgnored(BiasedAssertionDirective::kAssume));

  EXPECT_TRUE(BiasedDistActsAsInside(BiasedAssertionDirective::kAssert));
  EXPECT_TRUE(BiasedDistActsAsInside(BiasedAssertionDirective::kCover));
  EXPECT_FALSE(BiasedDistActsAsInside(BiasedAssertionDirective::kAssume));
}

TEST(AssumeStatement, AssumedPropertyHoldsSameWithOrWithoutBiasing) {
  std::vector<int64_t> members = {0, 1};
  EXPECT_TRUE(AssumeValueIsLegalUnderBiasing(0, members, true));
  EXPECT_TRUE(AssumeValueIsLegalUnderBiasing(0, members, false));
  EXPECT_TRUE(AssumeValueIsLegalUnderBiasing(1, members, true));
  EXPECT_FALSE(AssumeValueIsLegalUnderBiasing(2, members, true));
}

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

TEST(AssumeStatement, ActionControlDoesNotResurrectDisabledBranch) {
  EXPECT_EQ(ResolveAssumeActionUnderControl(AssertActionBlockChoice::kNone,
                                            true, true),
            AssertActionBlockChoice::kNone);
}

TEST(AssumeStatement, ControlKeepsPassBranchWhenEnabled) {
  EXPECT_EQ(ResolveAssumeActionUnderControl(AssertActionBlockChoice::kPass,
                                            true, true),
            AssertActionBlockChoice::kPass);
}

TEST(AssumeStatement, NoLegalValuesRejectsEveryCandidate) {
  std::vector<int64_t> empty_members;
  EXPECT_FALSE(AssumeValueIsLegalUnderBiasing(0, empty_members, true));
  EXPECT_FALSE(AssumeValueIsLegalUnderBiasing(0, empty_members, false));
}

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
