#include <gtest/gtest.h>

#include "elaborator/sampled_value.h"

using namespace delta;

namespace {

TEST(SampledValueFunctions, RecognizesEveryProvidedFunction) {
  // §16.9.3: the provided sampled value functions are $sampled, $rose, $fell,
  // $stable, $changed, and $past.
  SampledValueFunction fn{};
  EXPECT_TRUE(ClassifySampledValueFunction("$sampled", fn));
  EXPECT_EQ(fn, SampledValueFunction::kSampled);
  EXPECT_TRUE(ClassifySampledValueFunction("$rose", fn));
  EXPECT_EQ(fn, SampledValueFunction::kRose);
  EXPECT_TRUE(ClassifySampledValueFunction("$fell", fn));
  EXPECT_EQ(fn, SampledValueFunction::kFell);
  EXPECT_TRUE(ClassifySampledValueFunction("$stable", fn));
  EXPECT_EQ(fn, SampledValueFunction::kStable);
  EXPECT_TRUE(ClassifySampledValueFunction("$changed", fn));
  EXPECT_EQ(fn, SampledValueFunction::kChanged);
  EXPECT_TRUE(ClassifySampledValueFunction("$past", fn));
  EXPECT_EQ(fn, SampledValueFunction::kPast);
}

TEST(SampledValueFunctions, RejectsNonSampledValueNames) {
  EXPECT_FALSE(IsSampledValueFunction("$display"));
  EXPECT_FALSE(IsSampledValueFunction("$rose_gclk"));
  EXPECT_FALSE(IsSampledValueFunction("rose"));
}

TEST(SampledValueFunctions, ValueChangeFunctionsAreRoseFellStableChanged) {
  // §16.9.3: $rose, $fell, $stable, and $changed are the value change
  // functions; $sampled and $past are not.
  EXPECT_TRUE(IsValueChangeFunction(SampledValueFunction::kRose));
  EXPECT_TRUE(IsValueChangeFunction(SampledValueFunction::kFell));
  EXPECT_TRUE(IsValueChangeFunction(SampledValueFunction::kStable));
  EXPECT_TRUE(IsValueChangeFunction(SampledValueFunction::kChanged));
  EXPECT_FALSE(IsValueChangeFunction(SampledValueFunction::kSampled));
  EXPECT_FALSE(IsValueChangeFunction(SampledValueFunction::kPast));
}

TEST(SampledValueFunctions, OnlySampledOmitsTheClockingEvent) {
  // §16.9.3: the clocking event is required for the semantics of $past, $rose,
  // $stable, $changed, and $fell; $sampled does not use a clocking event.
  EXPECT_FALSE(
      SampledValueFunctionUsesClockingEvent(SampledValueFunction::kSampled));
  EXPECT_TRUE(
      SampledValueFunctionUsesClockingEvent(SampledValueFunction::kRose));
  EXPECT_TRUE(
      SampledValueFunctionUsesClockingEvent(SampledValueFunction::kFell));
  EXPECT_TRUE(
      SampledValueFunctionUsesClockingEvent(SampledValueFunction::kStable));
  EXPECT_TRUE(
      SampledValueFunctionUsesClockingEvent(SampledValueFunction::kChanged));
  EXPECT_TRUE(
      SampledValueFunctionUsesClockingEvent(SampledValueFunction::kPast));
}

TEST(SampledValueFunctions, ValueChangeResultsAreBoolean) {
  // §16.9.3: the result of a value change function is true or false and may be
  // used as a Boolean expression.
  EXPECT_TRUE(SampledValueFunctionResultIsBoolean(SampledValueFunction::kRose));
  EXPECT_TRUE(
      SampledValueFunctionResultIsBoolean(SampledValueFunction::kChanged));
  EXPECT_FALSE(
      SampledValueFunctionResultIsBoolean(SampledValueFunction::kSampled));
  EXPECT_FALSE(
      SampledValueFunctionResultIsBoolean(SampledValueFunction::kPast));
}

TEST(SampledValueFunctions, LocalVariableAndMatchedAreRejectedInArguments) {
  // §16.9.3: local variables and the sequence method `matched` are not allowed
  // in the argument expressions passed to these functions.
  EXPECT_TRUE(SampledValueArgumentIsLegal(
      /*argument_uses_local_variable=*/false,
      /*argument_uses_matched_method=*/false));
  EXPECT_FALSE(SampledValueArgumentIsLegal(
      /*argument_uses_local_variable=*/true,
      /*argument_uses_matched_method=*/false));
  EXPECT_FALSE(SampledValueArgumentIsLegal(
      /*argument_uses_local_variable=*/false,
      /*argument_uses_matched_method=*/true));
  EXPECT_FALSE(SampledValueArgumentIsLegal(
      /*argument_uses_local_variable=*/true,
      /*argument_uses_matched_method=*/true));
}

TEST(SampledValueFunctions, PastNumberOfTicksMustBeOneOrGreater) {
  // §16.9.3: number_of_ticks shall be 1 or greater.
  EXPECT_FALSE(IsPastNumberOfTicksWellFormed(0));
  EXPECT_FALSE(IsPastNumberOfTicksWellFormed(-3));
  EXPECT_TRUE(IsPastNumberOfTicksWellFormed(1));
  EXPECT_TRUE(IsPastNumberOfTicksWellFormed(7));
}

TEST(SampledValueFunctions, PastFallsBackToDefaultSampledValue) {
  // §16.9.3: $past returns the default sampled value of expression1 when fewer
  // than number_of_ticks qualifying strictly prior time steps exist.
  EXPECT_TRUE(PastUsesDefaultSampledValue(/*number_of_ticks=*/1,
                                          /*available_prior_ticks=*/0));
  EXPECT_TRUE(PastUsesDefaultSampledValue(/*number_of_ticks=*/2,
                                          /*available_prior_ticks=*/0));
  EXPECT_TRUE(PastUsesDefaultSampledValue(/*number_of_ticks=*/2,
                                          /*available_prior_ticks=*/1));
  EXPECT_FALSE(PastUsesDefaultSampledValue(/*number_of_ticks=*/2,
                                           /*available_prior_ticks=*/2));
  EXPECT_FALSE(PastUsesDefaultSampledValue(/*number_of_ticks=*/1,
                                           /*available_prior_ticks=*/5));
}

TEST(SampledValueFunctions, PastArgumentsHaveStandardDefaults) {
  // §16.9.3: number_of_ticks defaults to 1 and expression2 defaults to 1'b1.
  EXPECT_EQ(kDefaultPastNumberOfTicks, 1);
  EXPECT_EQ(kDefaultPastGatingExpression, 1u);
}

TEST(SampledValueFunctions, AutomaticVariablesIllegalInClockAndGating) {
  // §16.9.3: $past may refer to automatic variables in its sampled expression,
  // but automatic variables are illegal in clocking events and in expression2.
  EXPECT_TRUE(PastArgumentMayReferenceAutomaticVariable(
      PastArgumentRole::kExpression1));
  EXPECT_FALSE(PastArgumentMayReferenceAutomaticVariable(
      PastArgumentRole::kGatingExpression));
  EXPECT_FALSE(PastArgumentMayReferenceAutomaticVariable(
      PastArgumentRole::kClockingEvent));
}

}  // namespace
