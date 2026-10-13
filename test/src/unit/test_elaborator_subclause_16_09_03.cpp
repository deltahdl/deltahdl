#include <gtest/gtest.h>

#include "elaborator/sampled_value.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

// §16.9.3: for a sampled value function other than $sampled whose clock is not
// given as an argument, the clocking event is inferred by the five rules keyed
// on the calling context. Each context resolves to its own inference source;
// bullet one defers to the §16.13.3 clock flow rules, and the last falls back
// to default clocking.
TEST(SampledValueFunctions, ClockInferenceFollowsCallingContext) {
  EXPECT_EQ(InferSampledValueClockingEvent(
                SampledValueClockContext::kAssertionSequenceOrProperty),
            SampledValueClockInference::kFromClockFlow);
  EXPECT_EQ(
      InferSampledValueClockingEvent(SampledValueClockContext::kActionBlock),
      SampledValueClockInference::kFromLeadingClock);
  EXPECT_EQ(
      InferSampledValueClockingEvent(SampledValueClockContext::kProcedure),
      SampledValueClockInference::kFromProceduralContext);
  EXPECT_EQ(InferSampledValueClockingEvent(
                SampledValueClockContext::kOutsideAssertion),
            SampledValueClockInference::kFromDefaultClocking);
}

// §16.9.3 (negative form): in a disable condition or a clock expression, no
// clocking event is inferred — the sampled value function shall be explicitly
// clocked. This is the closest input the rule must reject rather than resolve.
TEST(SampledValueFunctions, DisableConditionAndClockExprRequireExplicitClock) {
  EXPECT_EQ(InferSampledValueClockingEvent(
                SampledValueClockContext::kDisableConditionOrClockExpression),
            SampledValueClockInference::kRequiresExplicitClock);
}

// §16.9.3: the argument expressions of a sampled value function read no local
// variable and no matched: $stable(v) reads the local v of s, $rose(t.matched)
// the matched of t; $stable(a) reads neither.
TEST(SampledValueRules, ALocalOrMatchedInAnArgumentIsReported) {
  const char* const kReport =
      "may not reference a local variable or the sequence method matched";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a;\n"
      "  sequence t;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  sequence s;\n"
      "    int v;\n"
      "    @(posedge clk) (1, v = a) ##1 $stable(v);\n"
      "  endsequence\n"
      "  a1: assert property (@(posedge clk) $rose(t.matched));\n"
      "  a2: assert property (@(posedge clk) $stable(a));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 8, "16.9.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 10, "16.9.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 11, "16.9.3"));
}

// §16.9.3: $past's number_of_ticks is an elaboration-time constant of 1 or
// greater: the parameter Z folds to 0, the variable k folds to nothing, and
// the parameter N folds to 2.
TEST(SampledValueRules, APastNumberOfTicksIsAConstantOfOneOrMore) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter int Z = 0;\n"
      "  parameter int N = 2;\n"
      "  logic clk, a, b;\n"
      "  int k;\n"
      "  a1: assert property (@(posedge clk) $past(a, Z) == b);\n"
      "  a2: assert property (@(posedge clk) $past(a, k) == b);\n"
      "  a3: assert property (@(posedge clk) $past(a, N) == b);\n"
      "  a4: assert property (@(posedge clk) $past(a, , b) == b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the number_of_ticks of $past shall be 1 or "
                            "greater",
                            6, "16.9.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the number_of_ticks of $past shall be an "
                            "elaboration-time constant expression",
                            7, "16.9.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "number_of_ticks of $past",
                             8, "16.9.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "number_of_ticks of $past",
                             9, "16.9.3"));
}

// §16.9.3: an automatic variable may stand in $past's expression1 but not in
// its expression2, the gating expression.
TEST(SampledValueRules, AnAutomaticInPastsGateIsReported) {
  const char* const kReport =
      "an automatic variable may not stand in the clocking event or the "
      "expression2 of $past";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  always @(posedge clk) begin\n"
      "    automatic logic g = a;\n"
      "    a1: assert property ($past(b, 1, g) == a);\n"
      "    a2: assert property ($past(g, 1, b) == a);\n"
      "    a3: assert property ($rose(b, @(posedge g)));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 5, "16.9.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 6, "16.9.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an automatic variable may not stand in the "
                            "clocking event or the expression2 of $rose",
                            7, "16.9.3"));
}

// §16.9.3: outside an assertion, a sampled value function with no clocking
// event of its own takes the clock the procedure infers or the default
// clocking; an initial procedure infers none, so with no default clocking
// $rose there is illegal, and with one it is clocked by it.
TEST(SampledValueRules, AnUnclockedCallWithNoneInferableIsReported) {
  const char* const kReport = "$rose has no clocking event";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    b = $rose(a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 4, "16.9.3"));
  ElabFixture g;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  initial begin\n"
      "    b = $rose(a);\n"
      "  end\n"
      "endmodule\n",
      g);
  EXPECT_FALSE(ReportedError(g.diag.Diagnostics(), kReport, 5, "16.9.3"));
}

// §16.9.3: in a disable condition a sampled value function other than
// $sampled gives its clocking event explicitly.
TEST(SampledValueRules, AnUnclockedCallInADisableConditionIsReported) {
  const char* const kReport =
      "in a disable condition or a clocking event shall have its clocking "
      "event specified explicitly";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, rst, a;\n"
      "  a1: assert property (@(posedge clk) disable iff ($fell(rst)) a);\n"
      "  a2: assert property (@(posedge clk)\n"
      "    disable iff ($fell(rst, @(posedge clk))) a);\n"
      "  a3: assert property (@(posedge clk) disable iff ($sampled(rst)) a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 3, "16.9.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 5, "16.9.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 6, "16.9.3"));
}

}  // namespace
