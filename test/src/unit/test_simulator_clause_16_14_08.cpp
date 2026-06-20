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
  EXPECT_TRUE(NonvacuousDisjunctiveForm(/*left=*/true, /*right=*/false));
  EXPECT_TRUE(NonvacuousDisjunctiveForm(/*left=*/false, /*right=*/true));
  EXPECT_TRUE(NonvacuousDisjunctiveForm(/*left=*/true, /*right=*/true));
  EXPECT_FALSE(NonvacuousDisjunctiveForm(/*left=*/false, /*right=*/false));
}

// §16.14.8(g): a held guard takes the then-branch; the single-branch form with
// a false guard holds vacuously.
TEST(SvaNonvacuous, IfWithoutElse) {
  EXPECT_TRUE(NonvacuousIfElse(/*guard_holds=*/true, /*then=*/true,
                               /*has_else=*/false, /*else=*/true));
  EXPECT_FALSE(NonvacuousIfElse(/*guard_holds=*/true, /*then=*/false,
                                /*has_else=*/false, /*else=*/true));
  // False guard, no else: nothing to check, so the attempt is vacuous.
  EXPECT_FALSE(NonvacuousIfElse(/*guard_holds=*/false, /*then=*/true,
                                /*has_else=*/false, /*else=*/true));
}

// §16.14.8(g): with an else branch a false guard routes to the else-branch
// attempt and the attempt is nonvacuous when that branch is.
TEST(SvaNonvacuous, IfElseRoutesOnGuard) {
  EXPECT_TRUE(NonvacuousIfElse(/*guard_holds=*/false, /*then=*/false,
                               /*has_else=*/true, /*else=*/true));
  EXPECT_FALSE(NonvacuousIfElse(/*guard_holds=*/false, /*then=*/true,
                                /*has_else=*/true, /*else=*/false));
}

// §16.14.8(g): when the guard holds the then-branch attempt decides nonvacuity
// even if an else branch is present, so the else-branch nonvacuity is ignored.
TEST(SvaNonvacuous, IfElseHeldGuardIgnoresElse) {
  EXPECT_TRUE(NonvacuousIfElse(/*guard_holds=*/true, /*then=*/true,
                               /*has_else=*/true, /*else=*/false));
  EXPECT_FALSE(NonvacuousIfElse(/*guard_holds=*/true, /*then=*/false,
                                /*has_else=*/true, /*else=*/true));
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
  EXPECT_TRUE(NonvacuousNexttime(/*reachable=*/true, /*inner=*/true));
  EXPECT_FALSE(NonvacuousNexttime(/*reachable=*/false, /*inner=*/true));
  EXPECT_FALSE(NonvacuousNexttime(/*reachable=*/true, /*inner=*/false));
}

// §16.14.8(p)(q)(r): a covered clock event must witness a nonvacuous
// subproperty attempt with no earlier covered failure.
TEST(SvaNonvacuous, AlwaysNeedsWitnessWithoutPriorFailure) {
  EXPECT_TRUE(NonvacuousAlways(/*witness=*/true, /*prior_failure=*/false));
  EXPECT_FALSE(NonvacuousAlways(/*witness=*/false, /*prior_failure=*/false));
  EXPECT_FALSE(NonvacuousAlways(/*witness=*/true, /*prior_failure=*/true));
}

// §16.14.8(s)(t)(u): a covered clock event must witness a nonvacuous
// subproperty attempt with the subproperty not already holding earlier.
TEST(SvaNonvacuous, EventuallyNeedsWitnessWithoutPriorHold) {
  EXPECT_TRUE(NonvacuousEventually(/*witness=*/true, /*prior_hold=*/false));
  EXPECT_FALSE(NonvacuousEventually(/*witness=*/false, /*prior_hold=*/false));
  EXPECT_FALSE(NonvacuousEventually(/*witness=*/true, /*prior_hold=*/true));
}

// §16.14.8(v)(w): the non-overlapping until forms witness on either operand's
// attempt, require the right operand not to have held earlier, and require the
// left operand to have held at every earlier clock event.
TEST(SvaNonvacuous, UntilNonOverlappingWitnessesEitherOperand) {
  EXPECT_TRUE(NonvacuousUntil(/*overlapping=*/false, /*left_witness=*/false,
                              /*right_witness=*/true,
                              /*right_prior_hold=*/false,
                              /*left_holds_all_prior=*/true));
  EXPECT_TRUE(NonvacuousUntil(/*overlapping=*/false, /*left_witness=*/true,
                              /*right_witness=*/false,
                              /*right_prior_hold=*/false,
                              /*left_holds_all_prior=*/true));
  EXPECT_FALSE(NonvacuousUntil(/*overlapping=*/false, /*left_witness=*/false,
                               /*right_witness=*/false,
                               /*right_prior_hold=*/false,
                               /*left_holds_all_prior=*/true));
  EXPECT_FALSE(NonvacuousUntil(/*overlapping=*/false, /*left_witness=*/true,
                               /*right_witness=*/false,
                               /*right_prior_hold=*/true,
                               /*left_holds_all_prior=*/true));
  EXPECT_FALSE(NonvacuousUntil(/*overlapping=*/false, /*left_witness=*/true,
                               /*right_witness=*/false,
                               /*right_prior_hold=*/false,
                               /*left_holds_all_prior=*/false));
}

// §16.14.8(x)(y): the overlapping until_with forms witness only on the left
// operand's attempt.
TEST(SvaNonvacuous, UntilOverlappingWitnessesLeftOnly) {
  EXPECT_TRUE(NonvacuousUntil(/*overlapping=*/true, /*left_witness=*/true,
                              /*right_witness=*/false,
                              /*right_prior_hold=*/false,
                              /*left_holds_all_prior=*/true));
  EXPECT_FALSE(NonvacuousUntil(/*overlapping=*/true, /*left_witness=*/false,
                               /*right_witness=*/true,
                               /*right_prior_hold=*/false,
                               /*left_holds_all_prior=*/true));
}

// §16.14.8(z): `implies` needs a true and nonvacuous antecedent attempt and a
// nonvacuous consequent attempt.
TEST(SvaNonvacuous, ImpliesNeedsTrueNonvacuousAntecedent) {
  EXPECT_TRUE(NonvacuousImplies(/*ant_true=*/true, /*ant_nonvacuous=*/true,
                                /*con_nonvacuous=*/true));
  EXPECT_FALSE(NonvacuousImplies(/*ant_true=*/false, /*ant_nonvacuous=*/true,
                                 /*con_nonvacuous=*/true));
  EXPECT_FALSE(NonvacuousImplies(/*ant_true=*/true, /*ant_nonvacuous=*/false,
                                 /*con_nonvacuous=*/true));
  EXPECT_FALSE(NonvacuousImplies(/*ant_true=*/true, /*ant_nonvacuous=*/true,
                                 /*con_nonvacuous=*/false));
}

// §16.14.8(ab)(ac)(ad)(ae)(ag): an abort or disable-iff attempt is nonvacuous
// when the underlying attempt is nonvacuous and the condition never held across
// the steps it was evaluated at.
TEST(SvaNonvacuous, AbortOrDisableNeedsConditionNeverHeld) {
  EXPECT_TRUE(
      NonvacuousAbortOrDisable(/*inner=*/true, /*condition_held=*/false));
  EXPECT_FALSE(
      NonvacuousAbortOrDisable(/*inner=*/false, /*condition_held=*/false));
  EXPECT_FALSE(
      NonvacuousAbortOrDisable(/*inner=*/true, /*condition_held=*/true));
}

// §16.14.8(af): a case property is nonvacuous when a matching or default item
// is selected and that item's property_stmt attempt is nonvacuous.
TEST(SvaNonvacuous, CaseNeedsSelectedNonvacuousBranch) {
  EXPECT_TRUE(NonvacuousCase(/*selected=*/true, /*stmt_nonvacuous=*/true));
  EXPECT_FALSE(NonvacuousCase(/*selected=*/false, /*stmt_nonvacuous=*/true));
  EXPECT_FALSE(NonvacuousCase(/*selected=*/true, /*stmt_nonvacuous=*/false));
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
