#include <gtest/gtest.h>

#include "elaborator/concurrent_assertion_expr.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §16.6: an expression in a concurrent assertion shall not reference a chandle
// variable. Built from real source (a chandle declared with the chandle
// keyword, referenced in the property of a concurrent assert) and driven
// through elaboration so the rejection is observed end-to-end, not via a
// helper.
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

// §16.6 negative sibling: the same concurrent assert with an ordinary
// (non-chandle) variable in the chandle's place elaborates without error, so
// the rejection keys on the chandle type rather than the assertion context.
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

// §16.6 negative sibling: a chandle declared in the module but never named in
// the concurrent assertion does not trip the rule.
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

// §16.6: an expression in a concurrent assertion shall not reference a
// non-static class property, and `h.v` through a module's class handle is one,
// read here both directly and as the argument of a sampled value function.
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

// §16.6 names methods beside properties: a call of a non-static method
// through the handle is as illegal as a read of a non-static property.
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

// §16.6 negative sibling: the prohibition is on non-static members, so a
// static property, read through the handle or by the class scope, and one
// inherited from a base class, are accepted.
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
  // §16.6 frames the lifetime rule as automatic OR stateless: either alone
  // satisfies it, but a function with side effects is always disqualified.
  EXPECT_TRUE(FunctionEligibleInAssertionExpr(true, false, true));
  EXPECT_TRUE(FunctionEligibleInAssertionExpr(false, true, true));
  EXPECT_TRUE(FunctionEligibleInAssertionExpr(true, true, true));
  EXPECT_FALSE(FunctionEligibleInAssertionExpr(false, false, true));
  EXPECT_FALSE(FunctionEligibleInAssertionExpr(true, true, false));
  EXPECT_FALSE(FunctionEligibleInAssertionExpr(true, false, false));
  EXPECT_FALSE(FunctionEligibleInAssertionExpr(false, true, false));
  // Completes the 2x2x2 truth table: neither automatic nor stateless, and
  // has side effects — disqualified on both axes.
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

// §16.6: a function called in a concurrent assertion takes no output, inout
// or ref argument; peek writes n back, while look's const ref is allowed.
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

// §16.6: a function called in a concurrent assertion is automatic or keeps
// no state, and has no side effect: tally writes count, and keep holds n from
// one call to the next, while clean is automatic and writes its own local.
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

// §16.6: an increment or decrement in a concurrent assertion expression is a
// side effect; one in a match item assigning a local variable is allowed.
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
