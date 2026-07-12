#include <gtest/gtest.h>

#include "elaborator/inferred_clock_disable.h"

using namespace delta;

namespace {

TEST(InferredClockDisable, ClassifiesTheTwoSystemFunctions) {
  // §16.14.7: $inferred_clock and $inferred_disable are the inferred functions;
  // any other system-function name is neither.
  EXPECT_EQ(ClassifyInferredFunction("$inferred_clock"),
            InferredFunction::kClock);
  EXPECT_EQ(ClassifyInferredFunction("$inferred_disable"),
            InferredFunction::kDisable);
  EXPECT_EQ(ClassifyInferredFunction("$rose"), InferredFunction::kNone);
  EXPECT_EQ(ClassifyInferredFunction("$inferred"), InferredFunction::kNone);
}

TEST(InferredClockDisable, BothAreElaborationTimeFunctions) {
  // §16.14.7: both functions are elaboration-time system functions.
  EXPECT_TRUE(IsElaborationTimeInferredFunction(InferredFunction::kClock));
  EXPECT_TRUE(IsElaborationTimeInferredFunction(InferredFunction::kDisable));
  EXPECT_FALSE(IsElaborationTimeInferredFunction(InferredFunction::kNone));
}

TEST(InferredClockDisable, InferredClockIsResolvedEventExpression) {
  // §16.14.7: the inferred clocking event is the current resolved event
  // expression obtained by applying clock flow rules to the call site.
  auto r = ResolveInferredClock("posedge clk");
  EXPECT_FALSE(r.is_error);
  EXPECT_EQ(r.event, "posedge clk");
}

TEST(InferredClockDisable, InferredClockErrorsWhenNoEventInScope) {
  // §16.14.7: if there is no current resolved event expression when
  // $inferred_clock is encountered, an error shall be issued.
  auto r = ResolveInferredClock("");
  EXPECT_TRUE(r.is_error);
  EXPECT_TRUE(r.event.empty());
}

TEST(InferredClockDisable, InferredDisableUsesDefaultDisableInScope) {
  // §16.14.7: within the scope of a default disable iff declaration, the
  // inferred disable condition is that declaration's disable condition.
  EXPECT_EQ(
      ResolveInferredDisable(/*within_default_disable_scope=*/true, "rst"),
      "rst");
}

TEST(InferredClockDisable, InferredDisableIsFalseOutsideAnyScope) {
  // §16.14.7: outside the scope of any default disable iff declaration, the
  // call returns 1'b0 (false).
  EXPECT_EQ(
      ResolveInferredDisable(/*within_default_disable_scope=*/false, "ignored"),
      "1'b0");
}

TEST(InferredClockDisable, LegalOnlyAsEntireFormalDefaultOfAssertionDecl) {
  // §16.14.7: an inferred function may only be the entire default value
  // expression of a formal argument to a property, sequence, or checker
  // declaration.
  EXPECT_TRUE(InferredFunctionPlacementIsLegal(
      FormalArgumentOwner::kProperty,
      DefaultValuePosition::kEntireDefaultValue));
  EXPECT_TRUE(InferredFunctionPlacementIsLegal(
      FormalArgumentOwner::kSequence,
      DefaultValuePosition::kEntireDefaultValue));
  EXPECT_TRUE(InferredFunctionPlacementIsLegal(
      FormalArgumentOwner::kChecker,
      DefaultValuePosition::kEntireDefaultValue));
}

TEST(InferredClockDisable, IllegalAsPartialDefaultOrWrongOwner) {
  // §16.14.7: it is not legal as part of a larger default value expression,
  // outside any formal-argument default, or on a non-assertion declaration.
  EXPECT_FALSE(InferredFunctionPlacementIsLegal(
      FormalArgumentOwner::kProperty,
      DefaultValuePosition::kPartOfDefaultValue));
  EXPECT_FALSE(InferredFunctionPlacementIsLegal(
      FormalArgumentOwner::kProperty, DefaultValuePosition::kNotADefaultValue));
  EXPECT_FALSE(InferredFunctionPlacementIsLegal(
      FormalArgumentOwner::kOther, DefaultValuePosition::kEntireDefaultValue));
}

TEST(InferredClockDisable, ReplacementSourceFollowsInstantiationContext) {
  // §16.14.7: the call is replaced by the inferred expression determined at the
  // instantiation point, whose source depends on the context.
  EXPECT_EQ(InferredClockReplacementSource(
                InstantiationContext::kTopLevelAssertionInstance),
            InferredClockReplacement::kAssertionStatementLocation);
  EXPECT_EQ(InferredClockReplacementSource(
                InstantiationContext::kNestedPropertyInstance),
            InferredClockReplacement::kClockFlowUpToInstance);
  EXPECT_EQ(
      InferredClockReplacementSource(InstantiationContext::kCheckerInstance),
      InferredClockReplacement::kCheckerInstanceLocation);
}

}  // namespace
