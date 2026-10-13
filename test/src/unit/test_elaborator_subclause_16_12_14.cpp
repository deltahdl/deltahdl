#include <gtest/gtest.h>

#include "elaborator/abort_property.h"
#include "elaborator/sampled_value.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AbortProperty, RecognizesEveryAbortOperator) {
  // §16.12.14: a property is an abort property when it has one of the forms
  // accept_on, reject_on, sync_accept_on, or sync_reject_on.
  AbortOperator op{};
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

  EXPECT_TRUE(AbortConditionContentIsLegal(
      /*references_local_variable=*/false,
      /*references_triggered_method=*/false,
      /*references_matched_method=*/false));
  EXPECT_FALSE(AbortConditionContentIsLegal(
      /*references_local_variable=*/true, /*references_triggered_method=*/false,
      /*references_matched_method=*/false));
  EXPECT_FALSE(AbortConditionContentIsLegal(
      /*references_local_variable=*/false, /*references_triggered_method=*/true,
      /*references_matched_method=*/false));
  EXPECT_FALSE(AbortConditionContentIsLegal(
      /*references_local_variable=*/false,
      /*references_triggered_method=*/false,
      /*references_matched_method=*/true));
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
      SampledValueFunction::kSampled, /*clock_explicitly_specified=*/false));
  EXPECT_TRUE(AbortConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kSampled, /*clock_explicitly_specified=*/true));
  // Any other sampled value function needs the explicit clock argument.
  EXPECT_FALSE(AbortConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kChanged, /*clock_explicitly_specified=*/false));
  EXPECT_TRUE(AbortConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kChanged, /*clock_explicitly_specified=*/true));
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
    const bool kClockExplicit =
        AbortConditionSampledValueRequiresExplicitClock(fn);
    EXPECT_TRUE(
        AbortConditionSampledValueClockIsWellFormed(fn, kClockExplicit));
  }
}

TEST(AbortProperty, ClassificationRejectsCaseVariantsAndEmptyKeyword) {
  // §16.12.14 (error/edge): the abort operators are spelled exactly; an empty
  // string, a case variant, or surrounding whitespace is not an abort operator.
  AbortOperator op{};
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
  EXPECT_FALSE(AbortConditionContentIsLegal(
      /*references_local_variable=*/true, /*references_triggered_method=*/true,
      /*references_matched_method=*/true));
}

// §16.12.14: an abort condition references no local variable and neither
// sequence method: the condition v == 1 reads the local v of p, and
// s.triggered a sequence method; c reads neither.
TEST(AbortConditionRules, ALocalOrSequenceMethodIsReported) {
  const char* const kReport =
      "an abort condition may not reference a local variable or the sequence "
      "methods triggered and matched";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  property p;\n"
      "    int v;\n"
      "    @(posedge clk) (1, v = b) |-> accept_on (v == 1) a;\n"
      "  endproperty\n"
      "  a1: assert property (@(posedge clk) reject_on (s.triggered) a);\n"
      "  a2: assert property (@(posedge clk) reject_on (c) a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 8, "16.12.14"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 10, "16.12.14"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 11, "16.12.14"));
}

// §16.12.14: a sampled value function other than $sampled in an abort
// condition gives its clocking event explicitly.
TEST(AbortConditionRules, AnUnclockedSampledValueCallIsReported) {
  const char* const kReport =
      "$rose in an abort condition shall have its clocking event specified "
      "explicitly";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, c;\n"
      "  a1: assert property (@(posedge clk) accept_on ($rose(c)) a);\n"
      "  a2: assert property (@(posedge clk)\n"
      "    accept_on ($rose(c, @(posedge clk))) a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 3, "16.12.14"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 5, "16.12.14"));
}

}  // namespace
