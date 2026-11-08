#include <gtest/gtest.h>

#include "elaborator/concurrent_assertion_expr.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConcurrentAssertionBooleanExpr, ChandleInAssertPropertyRejectedEndToEnd) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic clk;\n"
      "  chandle h;\n"
      "  assert property (@(posedge clk) h != null);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "concurrent assertion expression references chandle", 4, "16.6"));
}

TEST(ConcurrentAssertionBooleanExpr, OrdinaryVariableInAssertPropertyAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic clk, a;\n"
      "  assert property (@(posedge clk) a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConcurrentAssertionBooleanExpr, UnreferencedChandleDoesNotTripAssertRule) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic clk, a;\n"
      "  chandle h;\n"
      "  assert property (@(posedge clk) a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConcurrentAssertionBooleanExpr, NonStaticClassPropertyRejectedEndToEnd) {
  ElabFixture f;
  Elaborate(
      "class H; bit v = 1; endclass\n"
      "module m;\n"
      "  logic clk;\n"
      "  H h = new;\n"
      "  assert property (@(posedge clk) $past(h.v) || h.v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assertion expression references "
                            "non-static class member \"h.v\"",
                            5, "16.6"));
}

TEST(ConcurrentAssertionBooleanExpr, NonStaticClassMethodRejectedEndToEnd) {
  ElabFixture f;
  Elaborate(
      "class H;\n"
      "  bit v;\n"
      "  function bit get(); return v; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  logic clk;\n"
      "  H h = new;\n"
      "  assert property (@(posedge clk) h.get());\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assertion expression references "
                            "non-static class member \"h.get\"",
                            8, "16.6"));
}

TEST(ConcurrentAssertionBooleanExpr, StaticClassPropertyAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "class B; static bit s; endclass\n"
      "class H extends B; static bit v; endclass\n"
      "module m;\n"
      "  logic clk;\n"
      "  H h = new;\n"
      "  assert property (@(posedge clk) h.v || H::v || h.s);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConcurrentAssertionBooleanExpr,
     OverallResultMustBeCastCompatibleWithIntegral) {
  EXPECT_TRUE(ConcurrentAssertionExprTypeIsAcceptable(true));
  EXPECT_FALSE(ConcurrentAssertionExprTypeIsAcceptable(false));
}

TEST(ConcurrentAssertionBooleanExpr, SubexpressionTypeIsExemptFromRule) {
  EXPECT_TRUE(ConcurrentAssertionSubexprTypeIsExempt());
}

TEST(ConcurrentAssertionBooleanExpr,
     AutomaticVariableOnlyReferenceableInProceduralConcurrentAssertions) {
  EXPECT_TRUE(AutomaticVariableReferenceAllowed(true));
  EXPECT_FALSE(AutomaticVariableReferenceAllowed(false));
}

TEST(ConcurrentAssertionBooleanExpr, NonStaticClassMemberReferenceIsForbidden) {
  EXPECT_FALSE(NonStaticClassMemberReferenceAllowed());
}

TEST(ConcurrentAssertionBooleanExpr, ChandleReferenceIsForbidden) {
  EXPECT_FALSE(ChandleVariableReferenceAllowed());
}

TEST(ConcurrentAssertionBooleanExpr,
     SideEffectsAllowedOnlyInSequenceMatchItemWithLocalLvalue) {
  EXPECT_TRUE(SideEffectAllowed(true, true));
  EXPECT_FALSE(SideEffectAllowed(true, false));
  EXPECT_FALSE(SideEffectAllowed(false, true));
  EXPECT_FALSE(SideEffectAllowed(false, false));
}

TEST(ConcurrentAssertionBooleanExpr,
     FunctionArgKindFiltersOutputInoutRefAllowsConstRef) {
  EXPECT_TRUE(FunctionArgKindAllowedInAssertionExpr(FunctionArgKind::kInput));
  EXPECT_TRUE(
      FunctionArgKindAllowedInAssertionExpr(FunctionArgKind::kConstRef));
  EXPECT_FALSE(FunctionArgKindAllowedInAssertionExpr(FunctionArgKind::kOutput));
  EXPECT_FALSE(FunctionArgKindAllowedInAssertionExpr(FunctionArgKind::kInout));
  EXPECT_FALSE(FunctionArgKindAllowedInAssertionExpr(FunctionArgKind::kRef));
}

TEST(ConcurrentAssertionBooleanExpr,
     FunctionMustBeAutomaticOrStatelessAndHaveNoSideEffects) {
  EXPECT_TRUE(FunctionEligibleInAssertionExpr(true, false, true));
  EXPECT_TRUE(FunctionEligibleInAssertionExpr(false, true, true));
  EXPECT_TRUE(FunctionEligibleInAssertionExpr(true, true, true));
  EXPECT_FALSE(FunctionEligibleInAssertionExpr(false, false, true));
  EXPECT_FALSE(FunctionEligibleInAssertionExpr(true, true, false));
  EXPECT_FALSE(FunctionEligibleInAssertionExpr(true, false, false));
  EXPECT_FALSE(FunctionEligibleInAssertionExpr(false, true, false));
  EXPECT_FALSE(FunctionEligibleInAssertionExpr(false, false, false));
}

TEST(ConcurrentAssertionBooleanExpr,
     DisableConditionAllowsTriggeredAndOrdinaryButForbidsLocalAndMatched) {
  EXPECT_TRUE(
      DisableConditionRefAllowed(DisableConditionRefKind::kOrdinaryVariable));
  EXPECT_TRUE(
      DisableConditionRefAllowed(DisableConditionRefKind::kTriggeredMethod));
  EXPECT_FALSE(
      DisableConditionRefAllowed(DisableConditionRefKind::kLocalVariable));
  EXPECT_FALSE(
      DisableConditionRefAllowed(DisableConditionRefKind::kMatchedMethod));
}

TEST(AssertionFunctionCalls, AFunctionWritingAnArgumentBackIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a;\n"
      "  int seen;\n"
      "  function automatic bit peek(input bit x, output int n);\n"
      "    n = 1;\n"
      "    return x;\n"
      "  endfunction\n"
      "  function automatic bit look(const ref logic x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  a1: assert property (@(posedge clk) peek(a, seen));\n"
      "  a2: assert property (@(posedge clk) look(a));\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "has an output, inout or ref argument and cannot be called in a "
      "concurrent assertion";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 11, "16.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 12, "16.6"));
}

TEST(AssertionFunctionCalls, AFunctionWithStateOrASideEffectIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a;\n"
      "  int count;\n"
      "  function bit tally(bit x);\n"
      "    count = count + 1;\n"
      "    return x;\n"
      "  endfunction\n"
      "  function bit keep(bit x);\n"
      "    int n = 0;\n"
      "    return x;\n"
      "  endfunction\n"
      "  function automatic bit clean(bit x);\n"
      "    bit y;\n"
      "    y = !x;\n"
      "    return !y;\n"
      "  endfunction\n"
      "  a1: assert property (@(posedge clk) tally(a));\n"
      "  a2: assert property (@(posedge clk) keep(a));\n"
      "  a3: assert property (@(posedge clk) clean(a));\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "keeps state or has a side effect and cannot be called in a concurrent "
      "assertion";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 17, "16.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 18, "16.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 19, "16.6"));
}

TEST(AssertionFunctionCalls, AnIncrementInAnAssertionExpressionIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a;\n"
      "  int n;\n"
      "  a1: assert property (@(posedge clk) n++ < 10);\n"
      "  sequence s;\n"
      "    int x;\n"
      "    @(posedge clk) (a, x = 0) ##1 (a, x++);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "an increment or decrement in a concurrent assertion expression is a "
      "side effect";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 4, "16.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 7, "16.6"));
}

}  // namespace
