#include <gtest/gtest.h>

#include "elaborator/abort_property.h"

using namespace delta;

namespace {

TEST(AbortProperty, RecognizesEveryAbortOperator) {
  // §16.12.14: a property is an abort property when it has one of the forms
  // accept_on, reject_on, sync_accept_on, or sync_reject_on.
  AbortOperator op;
  EXPECT_TRUE(ClassifyAbortOperator("accept_on", op));
  EXPECT_EQ(op, AbortOperator::kAcceptOn);
  EXPECT_TRUE(ClassifyAbortOperator("reject_on", op));
  EXPECT_EQ(op, AbortOperator::kRejectOn);
  EXPECT_TRUE(ClassifyAbortOperator("sync_accept_on", op));
  EXPECT_EQ(op, AbortOperator::kSyncAcceptOn);
  EXPECT_TRUE(ClassifyAbortOperator("sync_reject_on", op));
  EXPECT_EQ(op, AbortOperator::kSyncRejectOn);
}

TEST(AbortProperty, RejectsNonAbortKeywords) {
  EXPECT_FALSE(IsAbortOperator("disable"));
  EXPECT_FALSE(IsAbortOperator("accept"));
  EXPECT_FALSE(IsAbortOperator("sync_on"));
}

TEST(AbortProperty, SyncFormsAreSynchronousAbortProperties) {
  // §16.12.14: accept_on and reject_on are the asynchronous abort properties;
  // sync_accept_on and sync_reject_on are the synchronous abort properties.
  EXPECT_FALSE(IsSynchronousAbort(AbortOperator::kAcceptOn));
  EXPECT_FALSE(IsSynchronousAbort(AbortOperator::kRejectOn));
  EXPECT_TRUE(IsSynchronousAbort(AbortOperator::kSyncAcceptOn));
  EXPECT_TRUE(IsSynchronousAbort(AbortOperator::kSyncRejectOn));
}

TEST(AbortProperty, AcceptFormsForceTrueAndRejectFormsForceFalse) {
  // §16.12.14: when the abort condition becomes true the accept forms make the
  // overall evaluation true and the reject forms make it false.
  EXPECT_TRUE(AbortConditionForcesTrue(AbortOperator::kAcceptOn));
  EXPECT_TRUE(AbortConditionForcesTrue(AbortOperator::kSyncAcceptOn));
  EXPECT_FALSE(AbortConditionForcesTrue(AbortOperator::kRejectOn));
  EXPECT_FALSE(AbortConditionForcesTrue(AbortOperator::kSyncRejectOn));
}

TEST(AbortProperty, NestingOfAbortOperatorsIsAllowed) {
  // §16.12.14: any nesting of accept_on, reject_on, sync_accept_on, and
  // sync_reject_on is allowed.
  EXPECT_TRUE(AbortOperatorsMayNest());
}

TEST(AbortProperty, AbortConditionForbidsLocalVariablesTriggeredAndMatched) {
  // §16.12.14: abort conditions shall not contain any reference to local
  // variables nor to the sequence methods triggered and matched.
  EXPECT_FALSE(AbortConditionAllowsLocalVariableReference());
  EXPECT_FALSE(AbortConditionAllowsTriggeredMethod());
  EXPECT_FALSE(AbortConditionAllowsMatchedMethod());

  EXPECT_TRUE(AbortConditionContentIsLegal(/*local=*/false, /*triggered=*/false,
                                           /*matched=*/false));
  EXPECT_FALSE(AbortConditionContentIsLegal(/*local=*/true, /*triggered=*/false,
                                            /*matched=*/false));
  EXPECT_FALSE(AbortConditionContentIsLegal(/*local=*/false, /*triggered=*/true,
                                            /*matched=*/false));
  EXPECT_FALSE(AbortConditionContentIsLegal(/*local=*/false,
                                            /*triggered=*/false,
                                            /*matched=*/true));
}

TEST(AbortProperty, NonSampledSampledValueFunctionsRequireExplicitClock) {
  // §16.12.14: the abort condition may contain sampled value functions (see
  // §16.9.3); when a function other than $sampled is used the clock argument
  // shall be explicitly specified.
  EXPECT_FALSE(AbortConditionSampledValueRequiresExplicitClock(
      SampledValueFunction::kSampled));
  EXPECT_TRUE(AbortConditionSampledValueRequiresExplicitClock(
      SampledValueFunction::kRose));
  EXPECT_TRUE(AbortConditionSampledValueRequiresExplicitClock(
      SampledValueFunction::kPast));

  // $sampled is well formed with or without an explicit clock argument.
  EXPECT_TRUE(AbortConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kSampled, /*clock_explicit=*/false));
  EXPECT_TRUE(AbortConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kSampled, /*clock_explicit=*/true));
  // Any other sampled value function needs the explicit clock argument.
  EXPECT_FALSE(AbortConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kChanged, /*clock_explicit=*/false));
  EXPECT_TRUE(AbortConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kChanged, /*clock_explicit=*/true));
}

TEST(AbortProperty, SampledValueFunctionsArePermittedInAbortConditions) {
  // §16.12.14: the abort condition may contain sampled value functions (see
  // §16.9.3). None of them is categorically forbidden — each is well formed
  // once its clock-argument requirement is satisfied (only $sampled may omit
  // it).
  for (SampledValueFunction fn :
       {SampledValueFunction::kSampled, SampledValueFunction::kRose,
        SampledValueFunction::kFell, SampledValueFunction::kStable,
        SampledValueFunction::kChanged, SampledValueFunction::kPast}) {
    const bool clock_explicit =
        AbortConditionSampledValueRequiresExplicitClock(fn);
    EXPECT_TRUE(
        AbortConditionSampledValueClockIsWellFormed(fn, clock_explicit));
  }
}

TEST(AbortProperty, ClassificationRejectsCaseVariantsAndEmptyKeyword) {
  // §16.12.14 (error/edge): the abort operators are spelled exactly; an empty
  // string, a case variant, or surrounding whitespace is not an abort operator.
  AbortOperator op;
  EXPECT_FALSE(ClassifyAbortOperator("", op));
  EXPECT_FALSE(IsAbortOperator("Accept_On"));
  EXPECT_FALSE(IsAbortOperator("SYNC_REJECT_ON"));
  EXPECT_FALSE(IsAbortOperator("accept_on "));
  EXPECT_FALSE(IsAbortOperator("reject"));
}

TEST(AbortProperty, AbortConditionRejectsAllForbiddenReferencesAtOnce) {
  // §16.12.14 (error/edge): an abort condition that references a local variable
  // and both the triggered and matched methods together is illegal — any one
  // forbidden reference is enough, so their combination is too.
  EXPECT_FALSE(AbortConditionContentIsLegal(/*local=*/true, /*triggered=*/true,
                                            /*matched=*/true));
}

}  // namespace
