#include <gtest/gtest.h>

#include "elaborator/checker_procedures.h"

using namespace delta;

namespace {

TEST(CheckerProcedures, OnlyInitialAlwaysAndFinalProceduresAreAllowed) {
  // §17.5: the procedures allowed inside a checker body are the initial,
  // always, and final procedures.
  EXPECT_TRUE(ProceduralBlockAllowedInChecker(ProceduralBlockKind::kInitial));
  EXPECT_TRUE(ProceduralBlockAllowedInChecker(ProceduralBlockKind::kFinal));
}

TEST(CheckerProcedures, OnlyTheThreeSpecializedAlwaysFormsAreAllowed) {
  // §17.5: of the always procedures, only always_comb, always_latch, and
  // always_ff are allowed in a checker; a general-purpose always is not.
  EXPECT_TRUE(
      ProceduralBlockAllowedInChecker(ProceduralBlockKind::kAlwaysComb));
  EXPECT_TRUE(
      ProceduralBlockAllowedInChecker(ProceduralBlockKind::kAlwaysLatch));
  EXPECT_TRUE(ProceduralBlockAllowedInChecker(ProceduralBlockKind::kAlwaysFf));
  EXPECT_FALSE(ProceduralBlockAllowedInChecker(ProceduralBlockKind::kAlways));
}

TEST(CheckerProcedures, InitialProcedureMayContainItsListedConstructs) {
  // §17.5: an initial procedure in a checker may contain let declarations and
  // immediate, deferred, and concurrent assertions.
  EXPECT_TRUE(
      CheckerInitialProcedureAllows(CheckerInitialContent::kLetDeclaration));
  EXPECT_TRUE(CheckerInitialProcedureAllows(
      CheckerInitialContent::kImmediateAssertion));
  EXPECT_TRUE(
      CheckerInitialProcedureAllows(CheckerInitialContent::kDeferredAssertion));
  EXPECT_TRUE(CheckerInitialProcedureAllows(
      CheckerInitialContent::kConcurrentAssertion));
}

TEST(CheckerProcedures, InitialProcedureTimingControlMustBeEventControl) {
  // §17.5: the only timing control an initial procedure in a checker may use is
  // an event control; delay- and wait-based timing controls are not allowed.
  EXPECT_TRUE(CheckerInitialProcedureAllows(
      CheckerInitialContent::kEventTimingControl));
  EXPECT_FALSE(CheckerInitialProcedureAllows(
      CheckerInitialContent::kDelayTimingControl));
  EXPECT_FALSE(
      CheckerInitialProcedureAllows(CheckerInitialContent::kWaitTimingControl));
}

TEST(CheckerProcedures, BlockingAssignmentLimitedToCombAndLatch) {
  // §17.5: blocking assignments are allowed in always_comb and always_latch
  // procedures only, not in always_ff.
  EXPECT_TRUE(
      CheckerAlwaysStatementAllowed(CheckerAlwaysStatement::kBlockingAssignment,
                                    CheckerAlwaysForm::kAlwaysComb));
  EXPECT_TRUE(
      CheckerAlwaysStatementAllowed(CheckerAlwaysStatement::kBlockingAssignment,
                                    CheckerAlwaysForm::kAlwaysLatch));
  EXPECT_FALSE(
      CheckerAlwaysStatementAllowed(CheckerAlwaysStatement::kBlockingAssignment,
                                    CheckerAlwaysForm::kAlwaysFf));
}

TEST(CheckerProcedures, TimingEventControlLimitedToAlwaysFf) {
  // §17.5: timing event control is allowed in always_ff procedures only.
  EXPECT_TRUE(
      CheckerAlwaysStatementAllowed(CheckerAlwaysStatement::kTimingEventControl,
                                    CheckerAlwaysForm::kAlwaysFf));
  EXPECT_FALSE(
      CheckerAlwaysStatementAllowed(CheckerAlwaysStatement::kTimingEventControl,
                                    CheckerAlwaysForm::kAlwaysComb));
  EXPECT_FALSE(
      CheckerAlwaysStatementAllowed(CheckerAlwaysStatement::kTimingEventControl,
                                    CheckerAlwaysForm::kAlwaysLatch));
}

TEST(CheckerProcedures, UnconditionalAlwaysStatementsAllowedInEveryForm) {
  // §17.5: nonblocking assignments, selection and loop statements, subroutine
  // calls, the three assertion kinds, and let declarations are allowed in every
  // checker always form.
  const CheckerAlwaysStatement unconditional[] = {
      CheckerAlwaysStatement::kNonblockingAssignment,
      CheckerAlwaysStatement::kSelectionStatement,
      CheckerAlwaysStatement::kLoopStatement,
      CheckerAlwaysStatement::kSubroutineCall,
      CheckerAlwaysStatement::kImmediateAssertion,
      CheckerAlwaysStatement::kDeferredAssertion,
      CheckerAlwaysStatement::kConcurrentAssertion,
      CheckerAlwaysStatement::kLetDeclaration,
  };
  const CheckerAlwaysForm forms[] = {
      CheckerAlwaysForm::kAlwaysComb,
      CheckerAlwaysForm::kAlwaysLatch,
      CheckerAlwaysForm::kAlwaysFf,
  };
  for (auto stmt : unconditional) {
    for (auto form : forms) {
      EXPECT_TRUE(CheckerAlwaysStatementAllowed(stmt, form));
    }
  }
}

TEST(CheckerProcedures, AlwaysFfSamplesEverythingButEventControl) {
  // §17.5: except for the variables used in the event control, all other
  // expressions in an always_ff procedure are sampled.
  EXPECT_TRUE(CheckerAlwaysExpressionIsSampled(
      CheckerAlwaysForm::kAlwaysFf, CheckerAlwaysExpressionPosition::kBody));
  EXPECT_FALSE(CheckerAlwaysExpressionIsSampled(
      CheckerAlwaysForm::kAlwaysFf,
      CheckerAlwaysExpressionPosition::kEventControl));
}

TEST(CheckerProcedures, CombAndLatchExpressionsAreNotImplicitlySampled) {
  // §17.5: expressions in always_comb and always_latch procedures are not
  // implicitly sampled; the assignments use the current values.
  for (auto pos : {CheckerAlwaysExpressionPosition::kBody,
                   CheckerAlwaysExpressionPosition::kEventControl}) {
    EXPECT_FALSE(
        CheckerAlwaysExpressionIsSampled(CheckerAlwaysForm::kAlwaysComb, pos));
    EXPECT_FALSE(
        CheckerAlwaysExpressionIsSampled(CheckerAlwaysForm::kAlwaysLatch, pos));
  }
}

TEST(CheckerProcedures, ClockInferenceDefersToTheSharedInferenceRules) {
  // §17.5: clock inference for checker procedures follows the rules in
  // §16.14.6; those rules are owned there, not redefined here.
  EXPECT_TRUE(CheckerProcedureClockInferenceFollowsSection16146());
}

TEST(CheckerProcedures, FinalProcedureMatchesModuleSemantics) {
  // §17.5: a final procedure may be specified within a checker in the same
  // manner as in a module, runs once at the end of simulation for every
  // instantiation, has no implied ordering with other final procedures, and is
  // independent of the checker's instantiation context.
  EXPECT_TRUE(CheckerFinalProcedureIsAllowed());
  EXPECT_TRUE(CheckerFinalProcedureRunsOncePerInstantiation());
  EXPECT_FALSE(CheckerFinalProceduresHaveImpliedOrdering());
  EXPECT_FALSE(CheckerFinalProcedureDependsOnInstantiationContext());
}

TEST(CheckerProcedures, FinalProcedureAdmitsExactlyNonCheckerFinalConstructs) {
  // §17.5: a final procedure within a checker may include any construct allowed
  // in a non-checker final procedure — and nothing a module final would reject.
  EXPECT_TRUE(CheckerFinalProcedureAllowsConstruct(
      /*allowed_in_non_checker_final=*/true));
  EXPECT_FALSE(CheckerFinalProcedureAllowsConstruct(
      /*allowed_in_non_checker_final=*/false));
}

}  // namespace
