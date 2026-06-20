#include <gtest/gtest.h>

#include "elaborator/multiclock_endpoint.h"
#include "elaborator/sequence_composition.h"
#include "elaborator/sequence_method.h"

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

}  // namespace
