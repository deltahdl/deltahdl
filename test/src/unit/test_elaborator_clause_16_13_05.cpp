#include <gtest/gtest.h>

#include "elaborator/multiclock_endpoint.h"
#include "elaborator/sequence_method.h"

using namespace delta;

namespace {

// §16.13.5: when triggered detects the end point of (or from within) a
// multiclocked sequence, the ending clock of the sequence instance to which
// triggered is applied shall be the same as the clock in the context where the
// application appears.
TEST(MulticlockEndPoint, TriggeredEndingClockMustMatchContextClock) {
  EXPECT_TRUE(TriggeredEndingClockMatchesContext(/*ending_clock=*/"clk",
                                                 /*context_clock=*/"clk"));
  EXPECT_FALSE(TriggeredEndingClockMatchesContext(/*ending_clock=*/"clk0",
                                                  /*context_clock=*/"clk1"));
}

// §16.13.5: matched detects a source sequence's end point when the source clock
// differs from the destination clock.
TEST(MulticlockEndPoint, MatchedDetectsEndPointWhenClocksDiffer) {
  EXPECT_TRUE(MatchedDetectsCrossClockEndPoint(/*source_clock=*/"clk",
                                               /*destination_clock=*/"sysclk"));
  EXPECT_FALSE(MatchedDetectsCrossClockEndPoint(/*source_clock=*/"clk",
                                                /*destination_clock=*/"clk"));
}

// §16.13.5: matched may be applied to a named sequence instance (with or
// without arguments), an untyped formal argument, or a formal argument of type
// `sequence` — the same operand kinds defined for the methods in §16.13.6.
TEST(MulticlockEndPoint, MatchedOperandMustBeNamedInstanceOrSequenceFormal) {
  EXPECT_TRUE(IsSequenceMethodOperandLegal(
      SequenceMethodOperandKind::kNamedSequenceInstance));
  EXPECT_TRUE(IsSequenceMethodOperandLegal(
      SequenceMethodOperandKind::kUntypedFormalArgument));
  EXPECT_TRUE(IsSequenceMethodOperandLegal(
      SequenceMethodOperandKind::kSequenceTypedFormalArgument));
  EXPECT_FALSE(IsSequenceMethodOperandLegal(SequenceMethodOperandKind::kOther));
}

// §16.13.5: the result of matched is a single-bit true/false value that does
// not depend on where the source sequence match began.
TEST(MulticlockEndPoint, MatchedResultIsSingleBitAndStartPointIndependent) {
  EXPECT_TRUE(SequenceMethodResultIsSingleBit());
  EXPECT_FALSE(SequenceMethodResultDependsOnStartPoint());
}

// §16.13.5: matched, like triggered, can be applied to sequences with formal
// arguments, and the local-variable rules match those of triggered.
TEST(MulticlockEndPoint, MatchedSupportsFormalsAndSharesLocalVarRules) {
  EXPECT_TRUE(MatchedAllowedOnSequenceWithFormalArguments());
  EXPECT_TRUE(MatchedLocalVariableRulesSameAsTriggered());
}

// §16.13.5: multiple matches in a single destination cycle are treated the same
// way as matching both disjuncts of an `or`.
TEST(MulticlockEndPoint, MatchedMultipleMatchesActLikeOrDisjuncts) {
  EXPECT_TRUE(MatchedMultipleMatchesTreatedAsOrDisjuncts());
}

// §16.13.5: unlike triggered, matched synchronizes between the two clocks by
// storing the source match until the first destination clock tick. This reuses
// the persistence model defined in §16.13.6.
TEST(MulticlockEndPoint, MatchedSynchronizesAcrossClocks) {
  EXPECT_TRUE(MatchedSynchronizesAcrossClocks());
  // triggered, by contrast, persists only through the time step.
  EXPECT_EQ(SequenceMethodStatusPersistence(SequenceMethod::kTriggered),
            SequenceMethodPersistence::kThroughTimeStep);
}

// §16.13.5 (shared §16.13.6 vocabulary): matched is restricted to sequence
// expressions, while triggered is also usable from procedural contexts.
TEST(MulticlockEndPoint, MatchedConfinedToSequenceExpressions) {
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kMatched, SequenceMethodContext::kSequenceExpression,
      /*sequence_treats_formal_as_local_var=*/false));
  EXPECT_FALSE(IsSequenceMethodContextLegal(
      SequenceMethod::kMatched,
      SequenceMethodContext::kBooleanExpressionOutsideSequence,
      /*sequence_treats_formal_as_local_var=*/false));
}

}  // namespace
