#include <gtest/gtest.h>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.14.8(a)(b)(c): an attempt of a bare sequence_expr, strong(sequence_expr),
// or weak(sequence_expr) is nonvacuous unconditionally.
TEST(SvaNonvacuous, SequenceFormAlwaysNonvacuous) {
  EXPECT_TRUE(NonvacuousSequenceForm());
}

// §16.14.8(d)(i): `not property_expr` and a property instance carry the
// nonvacuity of their single underlying attempt.
TEST(SvaNonvacuous, PassthroughMirrorsInner) {
  EXPECT_TRUE(NonvacuousPassthrough(/*inner_nonvacuous=*/true));
  EXPECT_FALSE(NonvacuousPassthrough(/*inner_nonvacuous=*/false));
}

// §16.14.8(e)(f)(aa): `or`, `and`, and `iff` are nonvacuous when either
// operand's underlying attempt is nonvacuous.
TEST(SvaNonvacuous, DisjunctiveFormTakesEitherOperand) {
  EXPECT_TRUE(NonvacuousDisjunctiveForm(/*left_nonvacuous=*/true,
                                        /*right_nonvacuous=*/false));
  EXPECT_TRUE(NonvacuousDisjunctiveForm(/*left_nonvacuous=*/false,
                                        /*right_nonvacuous=*/true));
  EXPECT_TRUE(NonvacuousDisjunctiveForm(/*left_nonvacuous=*/true,
                                        /*right_nonvacuous=*/true));
  EXPECT_FALSE(NonvacuousDisjunctiveForm(/*left_nonvacuous=*/false,
                                         /*right_nonvacuous=*/false));
}

// §16.14.8(g): a held guard takes the then-branch; the single-branch form with
// a false guard holds vacuously.
TEST(SvaNonvacuous, IfWithoutElse) {
  EXPECT_TRUE(NonvacuousIfElse(/*guard_holds=*/true, /*then_nonvacuous=*/true,
                               /*has_else=*/false, /*else_nonvacuous=*/true));
  EXPECT_FALSE(NonvacuousIfElse(/*guard_holds=*/true, /*then_nonvacuous=*/false,
                                /*has_else=*/false, /*else_nonvacuous=*/true));
  // False guard, no else: nothing to check, so the attempt is vacuous.
  EXPECT_FALSE(NonvacuousIfElse(/*guard_holds=*/false, /*then_nonvacuous=*/true,
                                /*has_else=*/false, /*else_nonvacuous=*/true));
}

// §16.14.8(g): with an else branch a false guard routes to the else-branch
// attempt and the attempt is nonvacuous when that branch is.
TEST(SvaNonvacuous, IfElseRoutesOnGuard) {
  EXPECT_TRUE(NonvacuousIfElse(/*guard_holds=*/false, /*then_nonvacuous=*/false,
                               /*has_else=*/true, /*else_nonvacuous=*/true));
  EXPECT_FALSE(NonvacuousIfElse(/*guard_holds=*/false, /*then_nonvacuous=*/true,
                                /*has_else=*/true, /*else_nonvacuous=*/false));
}

// §16.14.8(g): when the guard holds the then-branch attempt decides nonvacuity
// even if an else branch is present, so the else-branch nonvacuity is ignored.
TEST(SvaNonvacuous, IfElseHeldGuardIgnoresElse) {
  EXPECT_TRUE(NonvacuousIfElse(/*guard_holds=*/true, /*then_nonvacuous=*/true,
                               /*has_else=*/true, /*else_nonvacuous=*/false));
  EXPECT_FALSE(NonvacuousIfElse(/*guard_holds=*/true, /*then_nonvacuous=*/false,
                                /*has_else=*/true, /*else_nonvacuous=*/true));
}

// §16.14.8(h)(j)(k): the implication and followed-by forms need an antecedent
// match point and a nonvacuous consequent attempt from that point.
TEST(SvaNonvacuous, SequencePreconditionNeedsMatchAndConsequent) {
  EXPECT_TRUE(NonvacuousSequencePrecondition(/*antecedent_has_match=*/true,
                                             /*consequent_nonvacuous=*/true));
  EXPECT_FALSE(NonvacuousSequencePrecondition(/*antecedent_has_match=*/false,
                                              /*consequent_nonvacuous=*/true));
  EXPECT_FALSE(NonvacuousSequencePrecondition(/*antecedent_has_match=*/true,
                                              /*consequent_nonvacuous=*/false));
}

// §16.14.8(l)(m)(n)(o): the targeted future clock event must exist and the
// subproperty attempt beginning there must be nonvacuous; the weak/strong
// reading does not change nonvacuity.
TEST(SvaNonvacuous, NexttimeNeedsReachableTarget) {
  EXPECT_TRUE(NonvacuousNexttime(/*target_clock_event_reachable=*/true,
                                 /*inner_nonvacuous_at_target=*/true));
  EXPECT_FALSE(NonvacuousNexttime(/*target_clock_event_reachable=*/false,
                                  /*inner_nonvacuous_at_target=*/true));
  EXPECT_FALSE(NonvacuousNexttime(/*target_clock_event_reachable=*/true,
                                  /*inner_nonvacuous_at_target=*/false));
}

// §16.14.8(p)(q)(r): a covered clock event must witness a nonvacuous
// subproperty attempt with no earlier covered failure.
TEST(SvaNonvacuous, AlwaysNeedsWitnessWithoutPriorFailure) {
  EXPECT_TRUE(NonvacuousAlways(/*inner_nonvacuous_at_some_covered_event=*/true,
                               /*inner_fails_at_prior_covered_event=*/false));
  EXPECT_FALSE(
      NonvacuousAlways(/*inner_nonvacuous_at_some_covered_event=*/false,
                       /*inner_fails_at_prior_covered_event=*/false));
  EXPECT_FALSE(NonvacuousAlways(/*inner_nonvacuous_at_some_covered_event=*/true,
                                /*inner_fails_at_prior_covered_event=*/true));
}

// §16.14.8(s)(t)(u): a covered clock event must witness a nonvacuous
// subproperty attempt with the subproperty not already holding earlier.
TEST(SvaNonvacuous, EventuallyNeedsWitnessWithoutPriorHold) {
  EXPECT_TRUE(
      NonvacuousEventually(/*inner_nonvacuous_at_some_covered_event=*/true,
                           /*inner_holds_at_prior_covered_event=*/false));
  EXPECT_FALSE(
      NonvacuousEventually(/*inner_nonvacuous_at_some_covered_event=*/false,
                           /*inner_holds_at_prior_covered_event=*/false));
  EXPECT_FALSE(
      NonvacuousEventually(/*inner_nonvacuous_at_some_covered_event=*/true,
                           /*inner_holds_at_prior_covered_event=*/true));
}

// §16.14.8(v)(w): the non-overlapping until forms witness on either operand's
// attempt, require the right operand not to have held earlier, and require the
// left operand to have held at every earlier clock event.
TEST(SvaNonvacuous, UntilNonOverlappingWitnessesEitherOperand) {
  EXPECT_TRUE(NonvacuousUntil(/*overlapping=*/false,
                              /*left_nonvacuous_at_witness=*/false,
                              /*right_nonvacuous_at_witness=*/true,
                              /*right_holds_at_prior_event=*/false,
                              /*left_holds_at_all_prior_events=*/true));
  EXPECT_TRUE(NonvacuousUntil(/*overlapping=*/false,
                              /*left_nonvacuous_at_witness=*/true,
                              /*right_nonvacuous_at_witness=*/false,
                              /*right_holds_at_prior_event=*/false,
                              /*left_holds_at_all_prior_events=*/true));
  EXPECT_FALSE(NonvacuousUntil(/*overlapping=*/false,
                               /*left_nonvacuous_at_witness=*/false,
                               /*right_nonvacuous_at_witness=*/false,
                               /*right_holds_at_prior_event=*/false,
                               /*left_holds_at_all_prior_events=*/true));
  EXPECT_FALSE(NonvacuousUntil(/*overlapping=*/false,
                               /*left_nonvacuous_at_witness=*/true,
                               /*right_nonvacuous_at_witness=*/false,
                               /*right_holds_at_prior_event=*/true,
                               /*left_holds_at_all_prior_events=*/true));
  EXPECT_FALSE(NonvacuousUntil(/*overlapping=*/false,
                               /*left_nonvacuous_at_witness=*/true,
                               /*right_nonvacuous_at_witness=*/false,
                               /*right_holds_at_prior_event=*/false,
                               /*left_holds_at_all_prior_events=*/false));
}

// §16.14.8(x)(y): the overlapping until_with forms witness only on the left
// operand's attempt.
TEST(SvaNonvacuous, UntilOverlappingWitnessesLeftOnly) {
  EXPECT_TRUE(NonvacuousUntil(/*overlapping=*/true,
                              /*left_nonvacuous_at_witness=*/true,
                              /*right_nonvacuous_at_witness=*/false,
                              /*right_holds_at_prior_event=*/false,
                              /*left_holds_at_all_prior_events=*/true));
  EXPECT_FALSE(NonvacuousUntil(/*overlapping=*/true,
                               /*left_nonvacuous_at_witness=*/false,
                               /*right_nonvacuous_at_witness=*/true,
                               /*right_holds_at_prior_event=*/false,
                               /*left_holds_at_all_prior_events=*/true));
}

// §16.14.8(z): `implies` needs a true and nonvacuous antecedent attempt and a
// nonvacuous consequent attempt.
TEST(SvaNonvacuous, ImpliesNeedsTrueNonvacuousAntecedent) {
  EXPECT_TRUE(NonvacuousImplies(/*antecedent_true=*/true,
                                /*antecedent_nonvacuous=*/true,
                                /*consequent_nonvacuous=*/true));
  EXPECT_FALSE(NonvacuousImplies(/*antecedent_true=*/false,
                                 /*antecedent_nonvacuous=*/true,
                                 /*consequent_nonvacuous=*/true));
  EXPECT_FALSE(NonvacuousImplies(/*antecedent_true=*/true,
                                 /*antecedent_nonvacuous=*/false,
                                 /*consequent_nonvacuous=*/true));
  EXPECT_FALSE(NonvacuousImplies(/*antecedent_true=*/true,
                                 /*antecedent_nonvacuous=*/true,
                                 /*consequent_nonvacuous=*/false));
}

// §16.14.8(ab)(ac)(ad)(ae)(ag): an abort or disable-iff attempt is nonvacuous
// when the underlying attempt is nonvacuous and the condition never held across
// the steps it was evaluated at.
TEST(SvaNonvacuous, AbortOrDisableNeedsConditionNeverHeld) {
  EXPECT_TRUE(NonvacuousAbortOrDisable(
      /*inner_nonvacuous=*/true,
      /*condition_holds_at_any_evaluated_step=*/false));
  EXPECT_FALSE(NonvacuousAbortOrDisable(
      /*inner_nonvacuous=*/false,
      /*condition_holds_at_any_evaluated_step=*/false));
  EXPECT_FALSE(NonvacuousAbortOrDisable(
      /*inner_nonvacuous=*/true,
      /*condition_holds_at_any_evaluated_step=*/true));
}

// §16.14.8(af): a case property is nonvacuous when a matching or default item
// is selected and that item's property_stmt attempt is nonvacuous.
TEST(SvaNonvacuous, CaseNeedsSelectedNonvacuousBranch) {
  EXPECT_TRUE(NonvacuousCase(/*a_branch_selected=*/true,
                             /*selected_stmt_nonvacuous=*/true));
  EXPECT_FALSE(NonvacuousCase(/*a_branch_selected=*/false,
                              /*selected_stmt_nonvacuous=*/true));
  EXPECT_FALSE(NonvacuousCase(/*a_branch_selected=*/true,
                              /*selected_stmt_nonvacuous=*/false));
}

// §16.14.8: an attempt succeeds nonvacuously exactly when the property
// evaluates to true and the attempt is nonvacuous.
TEST(SvaNonvacuous, NonvacuousSuccessNeedsTrueAndNonvacuous) {
  EXPECT_TRUE(PropertySucceedsNonvacuously(/*property_true=*/true,
                                           /*attempt_nonvacuous=*/true));
  EXPECT_FALSE(PropertySucceedsNonvacuously(/*property_true=*/false,
                                            /*attempt_nonvacuous=*/true));
  EXPECT_FALSE(PropertySucceedsNonvacuously(/*property_true=*/true,
                                            /*attempt_nonvacuous=*/false));
}

}  // namespace
