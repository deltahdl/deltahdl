#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/sampled_value.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SampledValueFunctions, RecognizesEveryProvidedFunction) {
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
  EXPECT_TRUE(IsValueChangeFunction(SampledValueFunction::kRose));
  EXPECT_TRUE(IsValueChangeFunction(SampledValueFunction::kFell));
  EXPECT_TRUE(IsValueChangeFunction(SampledValueFunction::kStable));
  EXPECT_TRUE(IsValueChangeFunction(SampledValueFunction::kChanged));
  EXPECT_FALSE(IsValueChangeFunction(SampledValueFunction::kSampled));
  EXPECT_FALSE(IsValueChangeFunction(SampledValueFunction::kPast));
}

TEST(SampledValueFunctions, OnlySampledOmitsTheClockingEvent) {
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
  EXPECT_TRUE(SampledValueFunctionResultIsBoolean(SampledValueFunction::kRose));
  EXPECT_TRUE(
      SampledValueFunctionResultIsBoolean(SampledValueFunction::kChanged));
  EXPECT_FALSE(
      SampledValueFunctionResultIsBoolean(SampledValueFunction::kSampled));
  EXPECT_FALSE(
      SampledValueFunctionResultIsBoolean(SampledValueFunction::kPast));
}

TEST(SampledValueFunctions, LocalVariableAndMatchedAreRejectedInArguments) {
  EXPECT_TRUE(SampledValueArgumentIsLegal(false, false));
  EXPECT_FALSE(SampledValueArgumentIsLegal(true, false));
  EXPECT_FALSE(SampledValueArgumentIsLegal(false, true));
  EXPECT_FALSE(SampledValueArgumentIsLegal(true, true));
}

TEST(SampledValueFunctions, PastNumberOfTicksMustBeOneOrGreater) {
  EXPECT_FALSE(IsPastNumberOfTicksWellFormed(0));
  EXPECT_FALSE(IsPastNumberOfTicksWellFormed(-3));
  EXPECT_TRUE(IsPastNumberOfTicksWellFormed(1));
  EXPECT_TRUE(IsPastNumberOfTicksWellFormed(7));
}

TEST(SampledValueFunctions, PastFallsBackToDefaultSampledValue) {
  EXPECT_TRUE(PastUsesDefaultSampledValue(1, 0));
  EXPECT_TRUE(PastUsesDefaultSampledValue(2, 0));
  EXPECT_TRUE(PastUsesDefaultSampledValue(2, 1));
  EXPECT_FALSE(PastUsesDefaultSampledValue(2, 2));
  EXPECT_FALSE(PastUsesDefaultSampledValue(1, 5));
}

TEST(SampledValueFunctions, PastArgumentsHaveStandardDefaults) {
  EXPECT_EQ(kDefaultPastNumberOfTicks, 1);
  EXPECT_EQ(kDefaultPastGatingExpression, 1u);
}

TEST(SampledValueFunctions, AutomaticVariablesIllegalInClockAndGating) {
  EXPECT_TRUE(PastArgumentMayReferenceAutomaticVariable(
      PastArgumentRole::kExpression1));
  EXPECT_FALSE(PastArgumentMayReferenceAutomaticVariable(
      PastArgumentRole::kGatingExpression));
  EXPECT_FALSE(PastArgumentMayReferenceAutomaticVariable(
      PastArgumentRole::kClockingEvent));
}

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

TEST(SampledValueFunctions, DisableConditionAndClockExprRequireExplicitClock) {
  EXPECT_EQ(InferSampledValueClockingEvent(
                SampledValueClockContext::kDisableConditionOrClockExpression),
            SampledValueClockInference::kRequiresExplicitClock);
}

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

constexpr const char* kTicksReport =
    "the number_of_ticks of $past shall be 1 or greater";

std::ptrdiff_t TicksReportsOn(const std::vector<Diagnostic>& diags,
                              uint32_t line) {
  return std::ranges::count_if(diags, [line](const Diagnostic& d) {
    return d.loc.line == line &&
           d.message.find(kTicksReport) != std::string::npos;
  });
}

TEST(SampledValueRules, APastInsideAnOrGroupIsHeldToTheTicksRule) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  sequence s1;\n"
      "    @(posedge clk) a ##1 $past(b, 0);\n"
      "  endsequence\n"
      "  sequence s2;\n"
      "    @(posedge clk) a ##1 ($past(b, 0) or c);\n"
      "  endsequence\n"
      "  sequence s3;\n"
      "    @(posedge clk) a ##1 ($past(b, 1) or c);\n"
      "  endsequence\n"
      "  a1: assert property (@(posedge clk) a ##1 ($past(c, 0) or b) |-> a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kTicksReport, 4, "16.9.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kTicksReport, 7, "16.9.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kTicksReport, 10, "16.9.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kTicksReport, 12, "16.9.3"));
  EXPECT_EQ(TicksReportsOn(f.diag.Diagnostics(), 7), 1);
  EXPECT_EQ(TicksReportsOn(f.diag.Diagnostics(), 12), 1);
}

TEST(SampledValueRules, APastInsideASequenceActualIsHeldToTheTicksRule) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  sequence s(sequence q);\n"
      "    q ##1 c;\n"
      "  endsequence\n"
      "  a1: assert property (@(posedge clk) s(a ##1 $past(b, 0)));\n"
      "  a2: assert property (@(posedge clk) s(a ##1 $past(b, 1)));\n"
      "  a3: assert property (@(posedge clk) s($past(b, 0)));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kTicksReport, 6, "16.9.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kTicksReport, 7, "16.9.3"));
  EXPECT_EQ(TicksReportsOn(f.diag.Diagnostics(), 6), 1);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kTicksReport, 8, "16.9.3"));
  EXPECT_EQ(TicksReportsOn(f.diag.Diagnostics(), 8), 1);
}

}  // namespace
