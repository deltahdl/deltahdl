#include <gtest/gtest.h>

#include "elaborator/global_clocking_sampled_value.h"

using namespace delta;

namespace {

// §16.9.4: the provided functions are the past functions $past_gclk,
// $rose_gclk, $fell_gclk, $stable_gclk, $changed_gclk and the future functions
// $future_gclk, $rising_gclk, $falling_gclk, $steady_gclk, $changing_gclk.
TEST(GlobalClockingSampledFunctions, RecognizesEveryProvidedFunction) {
  GlobalClockingSampledFunction fn{};
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$past_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kPastGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$rose_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kRoseGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$fell_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kFellGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$stable_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kStableGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$changed_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kChangedGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$future_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kFutureGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$rising_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kRisingGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$falling_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kFallingGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$steady_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kSteadyGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$changing_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kChangingGclk);
}

// §16.9.4: a name that is not a global clocking sampled value function is not
// classified (e.g. the ordinary $past).
TEST(GlobalClockingSampledFunctions, RejectsNonGclkNames) {
  EXPECT_FALSE(IsGlobalClockingSampledFunction("$past"));
  EXPECT_FALSE(IsGlobalClockingSampledFunction("$rose"));
}

// §16.9.4: the past functions and future functions are partitioned by whether
// they use a past or a subsequent sampled value.
TEST(GlobalClockingSampledFunctions, PartitionsPastAndFuture) {
  EXPECT_TRUE(
      IsGlobalClockingPastFunction(GlobalClockingSampledFunction::kRoseGclk));
  EXPECT_FALSE(
      IsGlobalClockingFutureFunction(GlobalClockingSampledFunction::kRoseGclk));
  EXPECT_TRUE(IsGlobalClockingFutureFunction(
      GlobalClockingSampledFunction::kRisingGclk));
  EXPECT_FALSE(
      IsGlobalClockingPastFunction(GlobalClockingSampledFunction::kRisingGclk));
}

// §16.9.4: the functions may be used only if global clocking is defined.
TEST(GlobalClockingSampledFunctions, RequireGlobalClocking) {
  EXPECT_TRUE(GlobalClockingSampledFunctionUsable(true));
  EXPECT_FALSE(GlobalClockingSampledFunctionUsable(false));
}

// §16.9.4: the future functions may be invoked only in a property_expr or a
// sequence_expr; in particular not in an action block.
TEST(GlobalClockingSampledFunctions, FutureFunctionsLimitedToAssertionExprs) {
  EXPECT_TRUE(GlobalClockingFutureFunctionAllowedIn(
      GlobalClockingFunctionPlace::kPropertyExpr));
  EXPECT_TRUE(GlobalClockingFutureFunctionAllowedIn(
      GlobalClockingFunctionPlace::kSequenceExpr));
  EXPECT_FALSE(GlobalClockingFutureFunctionAllowedIn(
      GlobalClockingFunctionPlace::kActionBlock));
  EXPECT_FALSE(GlobalClockingFutureFunctionAllowedIn(
      GlobalClockingFunctionPlace::kProceduralCode));
}

// §16.9.4: the past functions are usable everywhere the ordinary sampled value
// functions are, including action blocks and general procedural code.
TEST(GlobalClockingSampledFunctions, PastFunctionsUsableInActionBlocks) {
  EXPECT_TRUE(GlobalClockingPastFunctionAllowedIn(
      GlobalClockingFunctionPlace::kActionBlock));
  EXPECT_TRUE(GlobalClockingPastFunctionAllowedIn(
      GlobalClockingFunctionPlace::kProceduralCode));
}

// §16.9.4: the future functions shall not be nested.
TEST(GlobalClockingSampledFunctions, FutureFunctionsMayNotNest) {
  EXPECT_TRUE(GlobalClockingFutureFunctionNestingAllowed(false));
  EXPECT_FALSE(GlobalClockingFutureFunctionNestingAllowed(true));
}

// §16.9.4: the future functions shall not be used in assertions containing
// sequence match items.
TEST(GlobalClockingSampledFunctions, FutureFunctionsRejectSequenceMatchItems) {
  EXPECT_TRUE(GlobalClockingFutureFunctionAllowedWithSequenceMatchItems(false));
  EXPECT_FALSE(GlobalClockingFutureFunctionAllowedWithSequenceMatchItems(true));
}

}  // namespace
