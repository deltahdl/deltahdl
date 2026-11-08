#include <gtest/gtest.h>

#include "simulator/sva_engine_properties.h"

using namespace delta;

namespace {

TEST(SvaNonvacuous, SequenceFormAlwaysNonvacuous) {
  EXPECT_TRUE(NonvacuousSequenceForm());
}

TEST(SvaNonvacuous, PassthroughMirrorsInner) {
  EXPECT_TRUE(NonvacuousPassthrough(true));
  EXPECT_FALSE(NonvacuousPassthrough(false));
}

TEST(SvaNonvacuous, DisjunctiveFormTakesEitherOperand) {
  EXPECT_TRUE(NonvacuousDisjunctiveForm(true, false));
  EXPECT_TRUE(NonvacuousDisjunctiveForm(false, true));
  EXPECT_TRUE(NonvacuousDisjunctiveForm(true, true));
  EXPECT_FALSE(NonvacuousDisjunctiveForm(false, false));
}

TEST(SvaNonvacuous, IfWithoutElse) {
  EXPECT_TRUE(NonvacuousIfElse(true, true, false, true));
  EXPECT_FALSE(NonvacuousIfElse(true, false, false, true));
  EXPECT_FALSE(NonvacuousIfElse(false, true, false, true));
}

TEST(SvaNonvacuous, IfElseRoutesOnGuard) {
  EXPECT_TRUE(NonvacuousIfElse(false, false, true, true));
  EXPECT_FALSE(NonvacuousIfElse(false, true, true, false));
}

TEST(SvaNonvacuous, IfElseHeldGuardIgnoresElse) {
  EXPECT_TRUE(NonvacuousIfElse(true, true, true, false));
  EXPECT_FALSE(NonvacuousIfElse(true, false, true, true));
}

TEST(SvaNonvacuous, SequencePreconditionNeedsMatchAndConsequent) {
  EXPECT_TRUE(NonvacuousSequencePrecondition(true, true));
  EXPECT_FALSE(NonvacuousSequencePrecondition(false, true));
  EXPECT_FALSE(NonvacuousSequencePrecondition(true, false));
}

TEST(SvaNonvacuous, NexttimeNeedsReachableTarget) {
  EXPECT_TRUE(NonvacuousNexttime(true, true));
  EXPECT_FALSE(NonvacuousNexttime(false, true));
  EXPECT_FALSE(NonvacuousNexttime(true, false));
}

TEST(SvaNonvacuous, AlwaysNeedsWitnessWithoutPriorFailure) {
  EXPECT_TRUE(NonvacuousAlways(true, false));
  EXPECT_FALSE(NonvacuousAlways(false, false));
  EXPECT_FALSE(NonvacuousAlways(true, true));
}

TEST(SvaNonvacuous, EventuallyNeedsWitnessWithoutPriorHold) {
  EXPECT_TRUE(NonvacuousEventually(true, false));
  EXPECT_FALSE(NonvacuousEventually(false, false));
  EXPECT_FALSE(NonvacuousEventually(true, true));
}

TEST(SvaNonvacuous, UntilNonOverlappingWitnessesEitherOperand) {
  EXPECT_TRUE(NonvacuousUntil(false, false, true, false, true));
  EXPECT_TRUE(NonvacuousUntil(false, true, false, false, true));
  EXPECT_FALSE(NonvacuousUntil(false, false, false, false, true));
  EXPECT_FALSE(NonvacuousUntil(false, true, false, true, true));
  EXPECT_FALSE(NonvacuousUntil(false, true, false, false, false));
}

TEST(SvaNonvacuous, UntilOverlappingWitnessesLeftOnly) {
  EXPECT_TRUE(NonvacuousUntil(true, true, false, false, true));
  EXPECT_FALSE(NonvacuousUntil(true, false, true, false, true));
}

TEST(SvaNonvacuous, ImpliesNeedsTrueNonvacuousAntecedent) {
  EXPECT_TRUE(NonvacuousImplies(true, true, true));
  EXPECT_FALSE(NonvacuousImplies(false, true, true));
  EXPECT_FALSE(NonvacuousImplies(true, false, true));
  EXPECT_FALSE(NonvacuousImplies(true, true, false));
}

TEST(SvaNonvacuous, AbortOrDisableNeedsConditionNeverHeld) {
  EXPECT_TRUE(NonvacuousAbortOrDisable(true, false));
  EXPECT_FALSE(NonvacuousAbortOrDisable(false, false));
  EXPECT_FALSE(NonvacuousAbortOrDisable(true, true));
}

TEST(SvaNonvacuous, CaseNeedsSelectedNonvacuousBranch) {
  EXPECT_TRUE(NonvacuousCase(true, true));
  EXPECT_FALSE(NonvacuousCase(false, true));
  EXPECT_FALSE(NonvacuousCase(true, false));
}

TEST(SvaNonvacuous, NonvacuousSuccessNeedsTrueAndNonvacuous) {
  EXPECT_TRUE(PropertySucceedsNonvacuously(true, true));
  EXPECT_FALSE(PropertySucceedsNonvacuously(false, true));
  EXPECT_FALSE(PropertySucceedsNonvacuously(true, false));
}

}  // namespace
