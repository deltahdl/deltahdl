#include <gtest/gtest.h>

#include "elaborator/abort_property.h"
#include "elaborator/sampled_value.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AbortProperty, RecognizesEveryAbortOperator) {
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
  EXPECT_FALSE(IsSynchronousAbort(AbortOperator::kAcceptOn));
  EXPECT_FALSE(IsSynchronousAbort(AbortOperator::kRejectOn));
  EXPECT_TRUE(IsSynchronousAbort(AbortOperator::kSyncAcceptOn));
  EXPECT_TRUE(IsSynchronousAbort(AbortOperator::kSyncRejectOn));
}

TEST(AbortProperty, AcceptFormsForceTrueAndRejectFormsForceFalse) {
  EXPECT_TRUE(AbortConditionForcesTrue(AbortOperator::kAcceptOn));
  EXPECT_TRUE(AbortConditionForcesTrue(AbortOperator::kSyncAcceptOn));
  EXPECT_FALSE(AbortConditionForcesTrue(AbortOperator::kRejectOn));
  EXPECT_FALSE(AbortConditionForcesTrue(AbortOperator::kSyncRejectOn));
}

TEST(AbortProperty, NestingOfAbortOperatorsIsAllowed) {
  EXPECT_TRUE(AbortOperatorsMayNest());
}

TEST(AbortProperty, AbortConditionForbidsLocalVariablesTriggeredAndMatched) {
  EXPECT_FALSE(AbortConditionAllowsLocalVariableReference());
  EXPECT_FALSE(AbortConditionAllowsTriggeredMethod());
  EXPECT_FALSE(AbortConditionAllowsMatchedMethod());

  EXPECT_TRUE(AbortConditionContentIsLegal(false, false, false));
  EXPECT_FALSE(AbortConditionContentIsLegal(true, false, false));
  EXPECT_FALSE(AbortConditionContentIsLegal(false, true, false));
  EXPECT_FALSE(AbortConditionContentIsLegal(false, false, true));
}

TEST(AbortProperty, NonSampledSampledValueFunctionsRequireExplicitClock) {
  EXPECT_FALSE(AbortConditionSampledValueRequiresExplicitClock(
      SampledValueFunction::kSampled));
  EXPECT_TRUE(AbortConditionSampledValueRequiresExplicitClock(
      SampledValueFunction::kRose));
  EXPECT_TRUE(AbortConditionSampledValueRequiresExplicitClock(
      SampledValueFunction::kPast));

  EXPECT_TRUE(AbortConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kSampled, false));
  EXPECT_TRUE(AbortConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kSampled, true));
  EXPECT_FALSE(AbortConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kChanged, false));
  EXPECT_TRUE(AbortConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kChanged, true));
}

TEST(AbortProperty, SampledValueFunctionsArePermittedInAbortConditions) {
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
  AbortOperator op{};
  EXPECT_FALSE(ClassifyAbortOperator("", op));
  EXPECT_FALSE(IsAbortOperator("Accept_On"));
  EXPECT_FALSE(IsAbortOperator("SYNC_REJECT_ON"));
  EXPECT_FALSE(IsAbortOperator("accept_on "));
  EXPECT_FALSE(IsAbortOperator("reject"));
}

TEST(AbortProperty, AbortConditionRejectsAllForbiddenReferencesAtOnce) {
  EXPECT_FALSE(AbortConditionContentIsLegal(true, true, true));
}

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
