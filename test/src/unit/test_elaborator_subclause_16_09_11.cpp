#include <gtest/gtest.h>

#include "elaborator/multiclock_endpoint.h"
#include "elaborator/sequence_composition.h"
#include "elaborator/sequence_method.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SequenceComposition, TwoCompositionMethodsAreValid) {
  EXPECT_TRUE(IsSequenceCompositionMethodValid(
      SequenceCompositionMethod::kNamedInstanceReference));
  EXPECT_TRUE(IsSequenceCompositionMethodValid(
      SequenceCompositionMethod::kTriggeredEndPointDetection));
}

TEST(SequenceComposition, NamedReferenceMatchesFromReferenceTick) {
  EXPECT_TRUE(NamedSequenceReferenceMatchesFromReferenceTick());
}

TEST(SequenceComposition, TriggeredEndPointOperandLegality) {
  EXPECT_TRUE(TriggeredEndPointOperandLegal(
      SequenceMethodOperandKind::kNamedSequenceInstance));
  EXPECT_TRUE(TriggeredEndPointOperandLegal(
      SequenceMethodOperandKind::kUntypedFormalArgument));
  EXPECT_TRUE(TriggeredEndPointOperandLegal(
      SequenceMethodOperandKind::kSequenceTypedFormalArgument));
  EXPECT_FALSE(
      TriggeredEndPointOperandLegal(SequenceMethodOperandKind::kOther));
}

TEST(SequenceComposition, TriggeredResultIsStartPointIndependent) {
  EXPECT_TRUE(SequenceMethodResultIsSingleBit());
  EXPECT_FALSE(SequenceMethodResultDependsOnStartPoint());
}

TEST(SequenceComposition, TriggeredEndingClockMatchesContextClock) {
  EXPECT_TRUE(TriggeredEndingClockMatchesContext("sysclk", "sysclk"));
  EXPECT_FALSE(TriggeredEndingClockMatchesContext("clk", "sysclk"));
}

TEST(SequenceComposition, EmptyMatchDoesNotActivateTriggered) {
  EXPECT_FALSE(EmptyMatchActivatesSequenceMethod());
}

TEST(TriggeredEndingClock, AnEndingClockOtherThanTheContextsIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, sysclk, a, b;\n"
      "  sequence e1;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  sequence e2;\n"
      "    @(posedge sysclk) a ##1 b;\n"
      "  endsequence\n"
      "  sequence rule;\n"
      "    @(posedge sysclk) a ##1 e1.triggered;\n"
      "  endsequence\n"
      "  sequence rule2;\n"
      "    @(posedge sysclk) a ##1 e2.triggered;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the ending clock of 'e1' differs from the clock "
                            "of the context its triggered stands in",
                            10, "16.9.11"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "the ending clock of 'e2'",
                             13, "16.9.11"));
}

TEST(TriggeredEndingClock, TheEndingClockIsTheLastClockTheSequenceWrites) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, sysclk, a, b;\n"
      "  sequence e3;\n"
      "    a ##1 b;\n"
      "  endsequence\n"
      "  sequence e4;\n"
      "    @(negedge sysclk) a ##1 b;\n"
      "  endsequence\n"
      "  sequence e5;\n"
      "    @(posedge clk) a ##1 @(posedge sysclk) b;\n"
      "  endsequence\n"
      "  sequence rule3;\n"
      "    @(posedge sysclk) a ##1 e3.triggered;\n"
      "  endsequence\n"
      "  sequence rule4;\n"
      "    @(posedge sysclk) a ##1 e4.triggered;\n"
      "  endsequence\n"
      "  sequence rule5;\n"
      "    @(posedge sysclk) a ##1 e5.triggered;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "the ending clock of 'e3'",
                             13, "16.9.11"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "the ending clock of 'e4'",
                            16, "16.9.11"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "the ending clock of 'e5'",
                             19, "16.9.11"));
}

TEST(TriggeredEndingClock, ATriggeredInAProcedureMeetsItsInferredClock) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, sysclk, a, b, x, y;\n"
      "  sequence e1;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  always @(posedge sysclk) x <= e1.triggered;\n"
      "  always @(posedge clk) y <= e1.triggered;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "the ending clock of 'e1'", 6,
                            "16.9.11"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "the ending clock of 'e1'",
                             7, "16.9.11"));
}

}  // namespace
