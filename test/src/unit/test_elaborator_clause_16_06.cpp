#include <gtest/gtest.h>

#include "elaborator/concurrent_assertion_expr.h"
#include "fixture_elaborator.h"

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
  EXPECT_TRUE(f.has_errors);
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

}  // namespace
