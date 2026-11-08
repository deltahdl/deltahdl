#include <gtest/gtest.h>

#include "elaborator/inferred_clock_disable.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(InferredClockDisable, ClassifiesTheTwoSystemFunctions) {
  EXPECT_EQ(ClassifyInferredFunction("$inferred_clock"),
            InferredFunction::kClock);
  EXPECT_EQ(ClassifyInferredFunction("$inferred_disable"),
            InferredFunction::kDisable);
  EXPECT_EQ(ClassifyInferredFunction("$rose"), InferredFunction::kNone);
  EXPECT_EQ(ClassifyInferredFunction("$inferred"), InferredFunction::kNone);
}

TEST(InferredClockDisable, BothAreElaborationTimeFunctions) {
  EXPECT_TRUE(IsElaborationTimeInferredFunction(InferredFunction::kClock));
  EXPECT_TRUE(IsElaborationTimeInferredFunction(InferredFunction::kDisable));
  EXPECT_FALSE(IsElaborationTimeInferredFunction(InferredFunction::kNone));
}

TEST(InferredClockDisable, InferredClockIsResolvedEventExpression) {
  auto r = ResolveInferredClock("posedge clk");
  EXPECT_FALSE(r.is_error);
  EXPECT_EQ(r.event, "posedge clk");
}

TEST(InferredClockDisable, InferredClockErrorsWhenNoEventInScope) {
  auto r = ResolveInferredClock("");
  EXPECT_TRUE(r.is_error);
  EXPECT_TRUE(r.event.empty());
}

TEST(InferredClockDisable, InferredDisableUsesDefaultDisableInScope) {
  EXPECT_EQ(ResolveInferredDisable(true, "rst"), "rst");
}

TEST(InferredClockDisable, InferredDisableIsFalseOutsideAnyScope) {
  EXPECT_EQ(ResolveInferredDisable(false, "ignored"), "1'b0");
}

TEST(InferredClockDisable, LegalOnlyAsEntireFormalDefaultOfAssertionDecl) {
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
  EXPECT_FALSE(InferredFunctionPlacementIsLegal(
      FormalArgumentOwner::kProperty,
      DefaultValuePosition::kPartOfDefaultValue));
  EXPECT_FALSE(InferredFunctionPlacementIsLegal(
      FormalArgumentOwner::kProperty, DefaultValuePosition::kNotADefaultValue));
  EXPECT_FALSE(InferredFunctionPlacementIsLegal(
      FormalArgumentOwner::kOther, DefaultValuePosition::kEntireDefaultValue));
}

TEST(InferredClockDisable, ReplacementSourceFollowsInstantiationContext) {
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

TEST(InferredClockDisable, AnInferredClockResolvingToNothingIsReported) {
  const char* const kReport =
      "$inferred_clock, the default of the formal 'clk' of 'p', has no "
      "resolved clocking event at this instance";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit a;\n"
      "  property p(clk = $inferred_clock);\n"
      "    @clk a;\n"
      "  endproperty\n"
      "  a1: assert property (p);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 6, "16.14.7"));
  ElabFixture g;
  ElaborateSrc(
      "module m;\n"
      "  bit a, clk;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  property p(clk = $inferred_clock);\n"
      "    @clk a;\n"
      "  endproperty\n"
      "  a1: assert property (p);\n"
      "endmodule\n",
      g);
  EXPECT_FALSE(ReportedError(g.diag.Diagnostics(), kReport, 7, "16.14.7"));
}

}  // namespace
