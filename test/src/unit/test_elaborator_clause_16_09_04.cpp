#include <gtest/gtest.h>

#include "elaborator/global_clocking_sampled_value.h"
#include "fixture_elaborator.h"

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

// §16.9.4: the global clocking sampled value functions may be used only if a
// global clocking is defined. A past function used in procedural code without
// any global clocking declaration in scope is rejected during elaboration.
TEST(GlobalClockingElab, GclkFunctionWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x;\n"
      "  always @(posedge clk) x = $past_gclk(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §16.9.4: with a global clocking declared in scope, the same past-function use
// in procedural code is accepted (the past functions are usable in general
// procedural code).
TEST(GlobalClockingElab, GclkFunctionWithGlobalClockingIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  always @(posedge clk) x = $past_gclk(x);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §16.9.4: the future functions may be invoked only in a property or sequence
// expression, so a future function in ordinary procedural code is rejected —
// even when a global clocking is defined (which isolates this from the
// requires-global-clocking rule). A past function in the same position is legal
// (see GclkFunctionWithGlobalClockingIsAccepted).
TEST(GlobalClockingElab, FutureFunctionInProceduralCodeErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x, y;\n"
      "  global clocking gc @(posedge clk); endclocking\n"
      "  always @(posedge clk) x = $future_gclk(y);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §16.9.4: "global clocking is defined" is resolved with the §14.14 scope
// rules, so the declaration need not be in the same module. A child instance
// that uses a past function but declares no global clocking of its own is
// accepted when an enclosing instance supplies one (§14.14 lookup rule b).
TEST(GlobalClockingElab, GclkFunctionResolvesGlobalClockingFromParentInstance) {
  ElabFixture f;
  ElaborateSrc(
      "module child;\n"
      "  logic clk;\n"
      "  logic [31:0] x;\n"
      "  always @(posedge clk) x = $past_gclk(x);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk;\n"
      "  global clocking gc @(posedge clk); endclocking\n"
      "  child c();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
