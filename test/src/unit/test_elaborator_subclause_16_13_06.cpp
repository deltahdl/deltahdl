#include <gtest/gtest.h>

#include <utility>
#include <vector>

#include "elaborator/sampled_value.h"
#include "elaborator/sequence_method.h"

using namespace delta;

namespace {

// §16.13.6: the operand of a sequence method shall be a named sequence
// instance, an untyped formal argument, or a formal argument of type
// `sequence`.
TEST(SequenceMethods, OperandMustBeNamedInstanceOrSequenceFormal) {
  EXPECT_TRUE(IsSequenceMethodOperandLegal(
      SequenceMethodOperandKind::kNamedSequenceInstance));
  EXPECT_TRUE(IsSequenceMethodOperandLegal(
      SequenceMethodOperandKind::kUntypedFormalArgument));
  EXPECT_TRUE(IsSequenceMethodOperandLegal(
      SequenceMethodOperandKind::kSequenceTypedFormalArgument));
  EXPECT_FALSE(IsSequenceMethodOperandLegal(SequenceMethodOperandKind::kOther));
}

// §16.13.6: the result of a sequence method is a single-bit true/false value
// that does not depend upon the starting point of the operand match.
TEST(SequenceMethods, ResultIsSingleBitAndStartPointIndependent) {
  EXPECT_TRUE(SequenceMethodResultIsSingleBit());
  EXPECT_FALSE(SequenceMethodResultDependsOnStartPoint());
}

// §16.13.6: triggered may be used in an assertion statement, a wait statement,
// or a Boolean expression outside a sequence context.
TEST(SequenceMethods, TriggeredLegalInAssertionWaitAndBooleanContexts) {
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered, SequenceMethodContext::kAssertionStatement,
      /*sequence_treats_formal_as_local_var=*/false));
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered, SequenceMethodContext::kWaitStatement,
      /*sequence_treats_formal_as_local_var=*/false));
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered,
      SequenceMethodContext::kBooleanExpressionOutsideSequence,
      /*sequence_treats_formal_as_local_var=*/false));
}

// §16.13.6: it is an error to invoke triggered outside a sequence context on a
// sequence that treats its formal arguments as local variables.
TEST(SequenceMethods, TriggeredOutsideSequenceWithLocalVarFormalIsError) {
  EXPECT_FALSE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered,
      SequenceMethodContext::kBooleanExpressionOutsideSequence,
      /*sequence_treats_formal_as_local_var=*/true));
  // The same sequence remains usable inside a sequence expression.
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered, SequenceMethodContext::kSequenceExpression,
      /*sequence_treats_formal_as_local_var=*/true));
}

// §16.13.6 (edge case): the local-variable restriction applies only when
// triggered is invoked outside a sequence context. A triggered call within an
// assertion's sequence/property expression is in a sequence context, so it
// stays legal even when the operand sequence treats its formal as a local
// variable — distinguishing the assertion-statement case from the wait/Boolean
// cases.
TEST(SequenceMethods, TriggeredInAssertionStaysLegalWithLocalVarFormal) {
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered, SequenceMethodContext::kAssertionStatement,
      /*sequence_treats_formal_as_local_var=*/true));
  // But the wait-statement use of the same sequence is rejected, because that
  // is outside a sequence context.
  EXPECT_FALSE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered, SequenceMethodContext::kWaitStatement,
      /*sequence_treats_formal_as_local_var=*/true));
}

// §16.13.6: a sequence treats its formal as a local variable when the formal is
// used as a match-item lvalue.
TEST(SequenceMethods, FormalIsLocalVarWhenUsedAsMatchItemLvalue) {
  EXPECT_TRUE(SequenceTreatsFormalAsLocalVar(
      /*formal_is_match_item_lvalue=*/true));
  EXPECT_FALSE(SequenceTreatsFormalAsLocalVar(
      /*formal_is_match_item_lvalue=*/false));
}

// §16.13.6: matched can only be used in sequence expressions.
TEST(SequenceMethods, MatchedLegalOnlyInSequenceExpressions) {
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kMatched, SequenceMethodContext::kSequenceExpression,
      /*sequence_treats_formal_as_local_var=*/false));
  EXPECT_FALSE(IsSequenceMethodContextLegal(
      SequenceMethod::kMatched, SequenceMethodContext::kAssertionStatement,
      /*sequence_treats_formal_as_local_var=*/false));
  EXPECT_FALSE(IsSequenceMethodContextLegal(
      SequenceMethod::kMatched, SequenceMethodContext::kWaitStatement,
      /*sequence_treats_formal_as_local_var=*/false));
  EXPECT_FALSE(IsSequenceMethodContextLegal(
      SequenceMethod::kMatched,
      SequenceMethodContext::kBooleanExpressionOutsideSequence,
      /*sequence_treats_formal_as_local_var=*/false));
}

// §16.13.6: the status is set in the Observed region; the sampled value of a
// method is its current value (§16.5.1).
TEST(SequenceMethods, StatusSetInObservedRegionAndSampledAsCurrentValue) {
  EXPECT_TRUE(SequenceMethodStatusSetInObservedRegion());
  EXPECT_TRUE(SequenceMethodSampledValueIsCurrentValue());
}

// §16.13.6: triggered persists through the remainder of the time step, while
// matched persists until the first destination clock tick after the match.
TEST(SequenceMethods, PersistenceDiffersBetweenTriggeredAndMatched) {
  EXPECT_EQ(SequenceMethodStatusPersistence(SequenceMethod::kTriggered),
            SequenceMethodPersistence::kThroughTimeStep);
  EXPECT_EQ(SequenceMethodStatusPersistence(SequenceMethod::kMatched),
            SequenceMethodPersistence::kUntilFirstDestinationClockTick);
}

// §16.13.6 / §16.9.11: an empty match shall not activate either method.
TEST(SequenceMethods, EmptyMatchDoesNotActivateMethods) {
  EXPECT_FALSE(EmptyMatchActivatesSequenceMethod());
}

// §16.13.6: there shall be no circular dependencies between sequences induced
// by the use of triggered.
TEST(SequenceMethods, TriggeredDependenciesMustBeAcyclic) {
  // a -> b -> c is a legal chain.
  const std::vector<std::pair<int, int>> kChain = {{0, 1}, {1, 2}};
  EXPECT_TRUE(TriggeredSequenceDependenciesAreAcyclic(3, kChain));
  // a -> b -> a closes a cycle and is illegal.
  const std::vector<std::pair<int, int>> kCycle = {{0, 1}, {1, 0}};
  EXPECT_FALSE(TriggeredSequenceDependenciesAreAcyclic(2, kCycle));
  // A self-dependency is also a cycle.
  const std::vector<std::pair<int, int>> kSelfLoop = {{0, 0}};
  EXPECT_FALSE(TriggeredSequenceDependenciesAreAcyclic(1, kSelfLoop));
}

// §16.13.6 (edge cases): the circularity check follows dependency chains of any
// length, and a sequence reachable through more than one path is not a cycle.
TEST(SequenceMethods,
     TriggeredDependencyCycleDetectionHandlesChainsAndDiamonds) {
  // A longer cycle a -> b -> c -> a is still illegal.
  const std::vector<std::pair<int, int>> kLongCycle = {{0, 1}, {1, 2}, {2, 0}};
  EXPECT_FALSE(TriggeredSequenceDependenciesAreAcyclic(3, kLongCycle));
  // A diamond a -> b, a -> c, b -> d, c -> d reaches d by two paths but has no
  // cycle, so it is legal.
  const std::vector<std::pair<int, int>> kDiamond = {
      {0, 1}, {0, 2}, {1, 3}, {2, 3}};
  EXPECT_TRUE(TriggeredSequenceDependenciesAreAcyclic(4, kDiamond));
  // No dependencies at all is trivially acyclic.
  EXPECT_TRUE(TriggeredSequenceDependenciesAreAcyclic(3, {}));
}

// §16.13.6: a sequence with a method either is explicitly clocked or infers its
// clock from the surrounding context (checker, module/interface/program port,
// function/task argument, event expression, or general §16.9.3 inference).
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

// §16.13.6: if $inferred_clock is the default for a formal and no actual is
// provided, the §16.9.3 inference rules determine the bound clocking event.
TEST(SequenceMethods, InferredClockDefaultAppliesWhenNoActualArgument) {
  EXPECT_TRUE(InferredClockDefaultUsesSampledValueRules(
      /*actual_argument_provided=*/false));
  EXPECT_FALSE(InferredClockDefaultUsesSampledValueRules(
      /*actual_argument_provided=*/true));
}

// §16.13.6 (cross-link to §16.9.3): it shall be considered an error to use the
// sequence method matched in a sampled value function. That rule is owned by
// §16.9.3; here we observe it through the shared sampled-value predicate.
TEST(SequenceMethods, MatchedInSampledValueFunctionIsError) {
  EXPECT_FALSE(SampledValueArgumentIsLegal(
      /*argument_uses_local_variable=*/false,
      /*argument_uses_matched_method=*/true));
  // A matched-free argument remains legal.
  EXPECT_TRUE(SampledValueArgumentIsLegal(
      /*argument_uses_local_variable=*/false,
      /*argument_uses_matched_method=*/false));
}

// §16.13.6 (weave with §16.9.3): a sequence on which a method is applied that
// is not explicitly clocked, and whose clock is not fixed by a
// §16.13.6-specific context (checker, module/interface/program port,
// function/task argument, event expression), infers its clocking event using
// the very same rules as §16.9.3 sampled value functions. Here we drive the
// shared §16.9.3 inference model directly to confirm §16.13.6 defers to it:
// outside an assertion it resolves to default clocking, and inside an assertion
// it defers in turn to the §16.13.3 clock flow rules.
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

}  // namespace
