#include <gtest/gtest.h>

#include <utility>
#include <vector>

#include "elaborator/sampled_value.h"
#include "elaborator/sequence_method.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SequenceMethods, OperandMustBeNamedInstanceOrSequenceFormal) {
  EXPECT_TRUE(IsSequenceMethodOperandLegal(
      SequenceMethodOperandKind::kNamedSequenceInstance));
  EXPECT_TRUE(IsSequenceMethodOperandLegal(
      SequenceMethodOperandKind::kUntypedFormalArgument));
  EXPECT_TRUE(IsSequenceMethodOperandLegal(
      SequenceMethodOperandKind::kSequenceTypedFormalArgument));
  EXPECT_FALSE(IsSequenceMethodOperandLegal(SequenceMethodOperandKind::kOther));
}

TEST(SequenceMethods, ResultIsSingleBitAndStartPointIndependent) {
  EXPECT_TRUE(SequenceMethodResultIsSingleBit());
  EXPECT_FALSE(SequenceMethodResultDependsOnStartPoint());
}

TEST(SequenceMethods, TriggeredLegalInAssertionWaitAndBooleanContexts) {
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered, SequenceMethodContext::kAssertionStatement,
      false));
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered, SequenceMethodContext::kWaitStatement,
      false));
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered,
      SequenceMethodContext::kBooleanExpressionOutsideSequence, false));
}

TEST(SequenceMethods, TriggeredOutsideSequenceWithLocalVarFormalIsError) {
  EXPECT_FALSE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered,
      SequenceMethodContext::kBooleanExpressionOutsideSequence, true));
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered, SequenceMethodContext::kSequenceExpression,
      true));
}

TEST(SequenceMethods, TriggeredInAssertionStaysLegalWithLocalVarFormal) {
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered, SequenceMethodContext::kAssertionStatement,
      true));
  EXPECT_FALSE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered, SequenceMethodContext::kWaitStatement, true));
}

TEST(SequenceMethods, FormalIsLocalVarWhenUsedAsMatchItemLvalue) {
  EXPECT_TRUE(SequenceTreatsFormalAsLocalVar(true));
  EXPECT_FALSE(SequenceTreatsFormalAsLocalVar(false));
}

TEST(SequenceMethods, MatchedLegalOnlyInSequenceExpressions) {
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kMatched, SequenceMethodContext::kSequenceExpression,
      false));
  EXPECT_FALSE(IsSequenceMethodContextLegal(
      SequenceMethod::kMatched, SequenceMethodContext::kAssertionStatement,
      false));
  EXPECT_FALSE(IsSequenceMethodContextLegal(
      SequenceMethod::kMatched, SequenceMethodContext::kWaitStatement, false));
  EXPECT_FALSE(IsSequenceMethodContextLegal(
      SequenceMethod::kMatched,
      SequenceMethodContext::kBooleanExpressionOutsideSequence, false));
}

TEST(SequenceMethods, StatusSetInObservedRegionAndSampledAsCurrentValue) {
  EXPECT_TRUE(SequenceMethodStatusSetInObservedRegion());
  EXPECT_TRUE(SequenceMethodSampledValueIsCurrentValue());
}

TEST(SequenceMethods, PersistenceDiffersBetweenTriggeredAndMatched) {
  EXPECT_EQ(SequenceMethodStatusPersistence(SequenceMethod::kTriggered),
            SequenceMethodPersistence::kThroughTimeStep);
  EXPECT_EQ(SequenceMethodStatusPersistence(SequenceMethod::kMatched),
            SequenceMethodPersistence::kUntilFirstDestinationClockTick);
}

TEST(SequenceMethods, EmptyMatchDoesNotActivateMethods) {
  EXPECT_FALSE(EmptyMatchActivatesSequenceMethod());
}

TEST(SequenceMethods, TriggeredDependenciesMustBeAcyclic) {
  const std::vector<std::pair<int, int>> kChain = {{0, 1}, {1, 2}};
  EXPECT_TRUE(TriggeredSequenceDependenciesAreAcyclic(3, kChain));
  const std::vector<std::pair<int, int>> kCycle = {{0, 1}, {1, 0}};
  EXPECT_FALSE(TriggeredSequenceDependenciesAreAcyclic(2, kCycle));
  const std::vector<std::pair<int, int>> kSelfLoop = {{0, 0}};
  EXPECT_FALSE(TriggeredSequenceDependenciesAreAcyclic(1, kSelfLoop));
}

TEST(SequenceMethods,
     TriggeredDependencyCycleDetectionHandlesChainsAndDiamonds) {
  const std::vector<std::pair<int, int>> kLongCycle = {{0, 1}, {1, 2}, {2, 0}};
  EXPECT_FALSE(TriggeredSequenceDependenciesAreAcyclic(3, kLongCycle));
  const std::vector<std::pair<int, int>> kDiamond = {
      {0, 1}, {0, 2}, {1, 3}, {2, 3}};
  EXPECT_TRUE(TriggeredSequenceDependenciesAreAcyclic(4, kDiamond));
  EXPECT_TRUE(TriggeredSequenceDependenciesAreAcyclic(3, {}));
}

TEST(SequenceMethods, ClockInferredFromContextUnlessExplicitlyClocked) {
  EXPECT_FALSE(SequenceMethodClockIsInferredFromContext(
      SequenceMethodClockContext::kExplicitlyClocked));
  EXPECT_TRUE(SequenceMethodClockIsInferredFromContext(
      SequenceMethodClockContext::kCheckerInstantiation));
  EXPECT_TRUE(SequenceMethodClockIsInferredFromContext(
      SequenceMethodClockContext::kModulePortConnection));
  EXPECT_TRUE(SequenceMethodClockIsInferredFromContext(
      SequenceMethodClockContext::kInterfaceOrProgramPortConnection));
  EXPECT_TRUE(SequenceMethodClockIsInferredFromContext(
      SequenceMethodClockContext::kFunctionOrTaskArgument));
  EXPECT_TRUE(SequenceMethodClockIsInferredFromContext(
      SequenceMethodClockContext::kEventExpressionInstance));
  EXPECT_TRUE(SequenceMethodClockIsInferredFromContext(
      SequenceMethodClockContext::kInferredFromSurroundingContext));
}

TEST(SequenceMethods, InferredClockDefaultAppliesWhenNoActualArgument) {
  EXPECT_TRUE(InferredClockDefaultUsesSampledValueRules(false));
  EXPECT_FALSE(InferredClockDefaultUsesSampledValueRules(true));
}

TEST(SequenceMethods, MatchedInSampledValueFunctionIsError) {
  EXPECT_FALSE(SampledValueArgumentIsLegal(false, true));
  EXPECT_TRUE(SampledValueArgumentIsLegal(false, false));
}

TEST(SequenceMethods, GeneralClockInferenceReusesSampledValueRules) {
  EXPECT_TRUE(SequenceMethodClockIsInferredFromContext(
      SequenceMethodClockContext::kInferredFromSurroundingContext));
  EXPECT_EQ(InferSampledValueClockingEvent(
                SampledValueClockContext::kOutsideAssertion),
            SampledValueClockInference::kFromDefaultClocking);
  EXPECT_EQ(InferSampledValueClockingEvent(
                SampledValueClockContext::kAssertionSequenceOrProperty),
            SampledValueClockInference::kFromClockFlow);
}

TEST(SequenceMethods, TriggeredOfAnUnclockedSequenceInADisableIsReported) {
  const char* const kReport =
      "triggered of the sequence 's', which has no explicit clocking event, "
      "may not stand in a disable condition";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  sequence s;\n"
      "    a ##1 b;\n"
      "  endsequence\n"
      "  sequence t;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  a1: assert property (@(posedge clk) disable iff (s.triggered) c);\n"
      "  a2: assert property (@(posedge clk) disable iff (t.triggered) c);\n"
      "  event ev;\n"
      "  a3: assert property (@(posedge clk) disable iff (ev.triggered) c);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 9, "16.13.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "triggered of the sequence",
                             12, "16.13.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "triggered of the sequence",
                             10, "16.13.6"));
}

TEST(SequenceMethods, TriggeredOutsideASequenceOnAnAssigningOneIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  int v;\n"
      "  sequence s(lv);\n"
      "    @(posedge clk) (a, lv = 1) ##1 a;\n"
      "  endsequence\n"
      "  sequence t;\n"
      "    int w;\n"
      "    @(posedge clk) a ##1 s(w).triggered;\n"
      "  endsequence\n"
      "  initial wait (s(v).triggered);\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "triggered may not be applied outside a sequence expression to 's'";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 11, "16.13.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 9, "16.13.6"));
}

TEST(SequenceMethods, ACycleThroughTriggeredIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  sequence s1;\n"
      "    @(posedge clk) a ##1 s2.triggered;\n"
      "  endsequence\n"
      "  sequence s2;\n"
      "    @(posedge clk) a ##1 s1.triggered;\n"
      "  endsequence\n"
      "  sequence s3;\n"
      "    @(posedge clk) a ##1 s4.triggered;\n"
      "  endsequence\n"
      "  sequence s4;\n"
      "    @(posedge clk) s5 ##1 s5;\n"
      "  endsequence\n"
      "  sequence s5;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the sequence 's1' depends on its own end point "
                            "through triggered",
                            3, "16.13.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "the sequence 's3' depends on its own end point",
                             9, "16.13.6"));
}

TEST(SequenceMethods, MatchedOutsideASequenceIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, x;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 a;\n"
      "  endsequence\n"
      "  initial wait (s.matched);\n"
      "  always @(posedge clk) x <= s.matched;\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "matched may be used only in a sequence expression";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 6, "16.13.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 7, "16.13.6"));
}

}  // namespace
