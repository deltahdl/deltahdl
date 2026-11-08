#include <gtest/gtest.h>

#include "elaborator/multiclock_endpoint.h"
#include "elaborator/sequence_method.h"

using namespace delta;

namespace {

TEST(MulticlockEndPoint, TriggeredEndingClockMustMatchContextClock) {
  EXPECT_TRUE(TriggeredEndingClockMatchesContext("clk", "clk"));
  EXPECT_FALSE(TriggeredEndingClockMatchesContext("clk0", "clk1"));
}

TEST(MulticlockEndPoint, MatchedDetectsEndPointWhenClocksDiffer) {
  EXPECT_TRUE(MatchedDetectsCrossClockEndPoint("clk", "sysclk"));
  EXPECT_FALSE(MatchedDetectsCrossClockEndPoint("clk", "clk"));
}

TEST(MulticlockEndPoint, MatchedOperandMustBeNamedInstanceOrSequenceFormal) {
  EXPECT_TRUE(IsSequenceMethodOperandLegal(
      SequenceMethodOperandKind::kNamedSequenceInstance));
  EXPECT_TRUE(IsSequenceMethodOperandLegal(
      SequenceMethodOperandKind::kUntypedFormalArgument));
  EXPECT_TRUE(IsSequenceMethodOperandLegal(
      SequenceMethodOperandKind::kSequenceTypedFormalArgument));
  EXPECT_FALSE(IsSequenceMethodOperandLegal(SequenceMethodOperandKind::kOther));
}

TEST(MulticlockEndPoint, MatchedResultIsSingleBitAndStartPointIndependent) {
  EXPECT_TRUE(SequenceMethodResultIsSingleBit());
  EXPECT_FALSE(SequenceMethodResultDependsOnStartPoint());
}

TEST(MulticlockEndPoint, MatchedSupportsFormalsAndSharesLocalVarRules) {
  EXPECT_TRUE(MatchedAllowedOnSequenceWithFormalArguments());
  EXPECT_TRUE(MatchedLocalVariableRulesSameAsTriggered());
}

TEST(MulticlockEndPoint, MatchedMultipleMatchesActLikeOrDisjuncts) {
  EXPECT_TRUE(MatchedMultipleMatchesTreatedAsOrDisjuncts());
}

TEST(MulticlockEndPoint, MatchedSynchronizesAcrossClocks) {
  EXPECT_TRUE(MatchedSynchronizesAcrossClocks());
  EXPECT_EQ(SequenceMethodStatusPersistence(SequenceMethod::kTriggered),
            SequenceMethodPersistence::kThroughTimeStep);
}

TEST(MulticlockEndPoint, MatchedConfinedToSequenceExpressions) {
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kMatched, SequenceMethodContext::kSequenceExpression,
      false));
  EXPECT_FALSE(IsSequenceMethodContextLegal(
      SequenceMethod::kMatched,
      SequenceMethodContext::kBooleanExpressionOutsideSequence, false));
}

}  // namespace
