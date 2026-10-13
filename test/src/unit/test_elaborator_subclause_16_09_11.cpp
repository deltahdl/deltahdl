#include <gtest/gtest.h>

#include "elaborator/multiclock_endpoint.h"
#include "elaborator/sequence_composition.h"
#include "elaborator/sequence_method.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §16.9.11: a complex sequence can be composed from simpler subsequences either
// by referencing a named sequence by name or by detecting another sequence's
// end point with triggered.
TEST(SequenceComposition, TwoCompositionMethodsAreValid) {
  EXPECT_TRUE(IsSequenceCompositionMethodValid(
      SequenceCompositionMethod::kNamedInstanceReference));
  EXPECT_TRUE(IsSequenceCompositionMethodValid(
      SequenceCompositionMethod::kTriggeredEndPointDetection));
}

// §16.9.11: referencing a named sequence requires it to match starting from the
// clock tick at which the reference is reached, not from the enclosing
// sequence's start.
TEST(SequenceComposition, NamedReferenceMatchesFromReferenceTick) {
  EXPECT_TRUE(NamedSequenceReferenceMatchesFromReferenceTick());
}

// §16.9.11: triggered may be applied to a named sequence instance, an untyped
// formal argument, or a formal argument of type `sequence`. This is the shared
// operand rule defined in §16.13.6.
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

// §16.9.11: triggered returns a single-bit value testing whether the operand
// has reached its end point; the result is independent of the operand's start
// point.
TEST(SequenceComposition, TriggeredResultIsStartPointIndependent) {
  EXPECT_TRUE(SequenceMethodResultIsSingleBit());
  EXPECT_FALSE(SequenceMethodResultDependsOnStartPoint());
}

// §16.9.11: triggered can be used in the presence of multiple clocks, but the
// ending clock of the sequence instance shall always be the same as the clock
// in the context where triggered appears. This is the same rule given in
// §16.13.5, shared through "elaborator/multiclock_endpoint.h".
TEST(SequenceComposition, TriggeredEndingClockMatchesContextClock) {
  EXPECT_TRUE(TriggeredEndingClockMatchesContext(/*ending_clock=*/"sysclk",
                                                 /*context_clock=*/"sysclk"));
  EXPECT_FALSE(TriggeredEndingClockMatchesContext(/*ending_clock=*/"clk",
                                                  /*context_clock=*/"sysclk"));
}

// §16.9.11: if a sequence admits an empty match, such empty matches shall not
// activate the triggered method.
TEST(SequenceComposition, EmptyMatchDoesNotActivateTriggered) {
  EXPECT_FALSE(EmptyMatchActivatesSequenceMethod());
}

// §16.9.11: the ending clock of a sequence triggered is applied to is the
// clock of its context: e1 ends on posedge clk, which rule's posedge sysclk
// is not, while e2 ends on posedge sysclk.
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

// §16.9.11: e4 ends on negedge sysclk, not the context's posedge sysclk; e5,
// multiclocked, ends on posedge sysclk, and e3, with no clock of its own,
// takes the context's.
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

// §16.9.11 with §16.14.6: in a procedure, the context's clock is the one the
// procedure infers: e1 ends on posedge clk, not the posedge sysclk of the
// first always, while the second always is clocked by posedge clk.
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
