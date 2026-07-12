#include <gtest/gtest.h>

#include "elaborator/checker_procedures.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(CheckerProcedures, OnlyInitialAlwaysAndFinalProceduresAreAllowed) {
  // §17.5: the procedures allowed inside a checker body are the initial,
  // always, and final procedures.
  EXPECT_TRUE(ProceduralBlockAllowedInChecker(ProceduralBlockKind::kInitial));
  EXPECT_TRUE(ProceduralBlockAllowedInChecker(ProceduralBlockKind::kFinal));
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
  const CheckerAlwaysStatement kUnconditional[] = {
      CheckerAlwaysStatement::kNonblockingAssignment,
      CheckerAlwaysStatement::kSelectionStatement,
      CheckerAlwaysStatement::kLoopStatement,
      CheckerAlwaysStatement::kSubroutineCall,
      CheckerAlwaysStatement::kImmediateAssertion,
      CheckerAlwaysStatement::kDeferredAssertion,
      CheckerAlwaysStatement::kConcurrentAssertion,
      CheckerAlwaysStatement::kLetDeclaration,
  };
  const CheckerAlwaysForm kForms[] = {
      CheckerAlwaysForm::kAlwaysComb,
      CheckerAlwaysForm::kAlwaysLatch,
      CheckerAlwaysForm::kAlwaysFf,
  };
  for (auto stmt : kUnconditional) {
    for (auto form : kForms) {
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

// §17.5, real-source elaboration of the rule that a checker admits only the
// always_comb/always_latch/always_ff forms. The predicate tests above model the
// decision table; these drive an actual checker declaration through the parser
// and elaborator so the production rejection/acceptance is observed on genuine
// source rather than a hand-built enum.

TEST(CheckerProcedures, GeneralAlwaysInCheckerBodyIsRejectedInElaboration) {
  // §17.5: a general 'always' procedure is not one of the always forms a
  // checker may contain, so the elaborator flags it. The checker is otherwise
  // valid, isolating the general-always form as the sole cause of the error.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic clk, input logic d);\n"
      "  logic q;\n"
      "  always @(posedge clk) q <= d;\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(CheckerProcedures, SpecializedAlwaysFormsInCheckerBodyElaborateCleanly) {
  // §17.5: the three permitted always forms — always_comb, always_latch, and
  // always_ff — are all accepted in a checker body. The same checker shape that
  // was rejected with a general always elaborates without error once each
  // procedure names an allowed form.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic clk, input logic en, input logic d);\n"
      "  logic q, c, l;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "  always_comb c = d & en;\n"
      "  always_latch if (en) l = d;\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §17.5, real-source elaboration of the rule that a checker final procedure is
// governed exactly as a module final procedure (§9.2.3): it admits any
// construct a non-checker final admits and nothing more. These drive a real
// checker final through the pipeline so the shared module-final validation is
// observed firing (and not firing) inside a checker.

TEST(CheckerProcedures, CheckerFinalRejectsConstructsAModuleFinalRejects) {
  // §17.5: a checker final admits only what a non-checker final admits. A
  // timing control is illegal in a module final (§9.2.3); placing one in a
  // checker final must be rejected the same way, showing the checker context
  // grants no exemption.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk;\n"
      "  final #5 $display(\"late\");\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(CheckerProcedures, CheckerFinalAdmitsWhatAModuleFinalAdmits) {
  // §17.5: the accepting side of the same equivalence — a checker final that
  // holds only constructs a module final permits (here a simple display call)
  // elaborates cleanly.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk;\n"
      "  final $display(\"done\");\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §17.5 lists the procedures a checker admits and the statements a checker
// always procedure may hold. The following drive each admitted input form,
// built from the real syntax of the dependency that supplies it, through the
// full parse+elaborate pipeline so the acceptance is observed on production and
// not just modeled in the decision table above. The general-always and final
// negatives are already exercised by the rejection tests earlier in this file;
// the remaining §17.5 restrictions (e.g. an initial timing control limited to
// an event control) are not enforced by production and so are covered only by
// the predicate model, not asserted as a runtime rejection here.

TEST(CheckerProcedures, CheckerInitialProcedureElaborates) {
  // §17.5: an initial procedure is one of the procedures a checker body admits.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk;\n"
      "  logic ok;\n"
      "  initial ok = 1'b0;\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerProcedures, CheckerInitialProcedureAdmitsEventControlTiming) {
  // §17.5: an initial procedure in a checker may use a procedural timing
  // control built from an event control (§9.4.2). The event control is the
  // produced input here, so it is written as real source and elaborated in
  // place.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic clk);\n"
      "  logic ok;\n"
      "  initial @(posedge clk) ok = 1'b1;\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerProcedures, CheckerAlwaysProcedureAdmitsCaseSelection) {
  // §17.5: a selection statement (§12.4/§12.5) is admitted in a checker always
  // procedure. A case statement with a default keeps the always_comb purely
  // combinational so only the selection form is under test.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic [1:0] sel, input logic a, input logic b);\n"
      "  logic y;\n"
      "  always_comb\n"
      "    case (sel)\n"
      "      2'b00: y = a;\n"
      "      default: y = b;\n"
      "    endcase\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerProcedures, CheckerAlwaysProcedureAdmitsLoopStatement) {
  // §17.5: a loop statement (§12.7) is admitted in a checker always procedure.
  // The for loop is built from real source and reduces its input
  // combinationally.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic [3:0] d);\n"
      "  logic p;\n"
      "  always_comb begin\n"
      "    p = 1'b0;\n"
      "    for (int i = 0; i < 4; i++) p = p ^ d[i];\n"
      "  end\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerProcedures, CheckerAlwaysProcedureAdmitsSubroutineCall) {
  // §17.5: a subroutine call (Clause 13) is admitted in a checker always
  // procedure. A system task call is invoked from an always_ff alongside the
  // nonblocking update, exercising the call form from real source.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic clk, input logic d);\n"
      "  logic q;\n"
      "  always_ff @(posedge clk) begin\n"
      "    q <= d;\n"
      "    $display(\"q=%b\", q);\n"
      "  end\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §17.5 restricts two forms that production now enforces in the elaborator: a
// blocking assignment is confined to always_comb/always_latch (not always_ff),
// and an initial procedure's only timing control is an event control. These
// drive the rejected form from real source; the accepting counterparts are the
// nonblocking always_ff and the event-controlled initial exercised above.

TEST(CheckerProcedures, BlockingAssignmentInCheckerAlwaysFfIsRejected) {
  // §17.5: blocking assignments are allowed in always_comb and always_latch
  // procedures only, so a blocking assignment in a checker always_ff is an
  // error. The nonblocking form of the same procedure elaborates cleanly
  // (SpecializedAlwaysFormsInCheckerBodyElaborateCleanly), isolating the
  // blocking assignment as the cause.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic clk, input logic d);\n"
      "  logic q;\n"
      "  always_ff @(posedge clk) q = d;\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(CheckerProcedures, CheckerInitialProcedureRejectsDelayTimingControl) {
  // §17.5: an initial procedure in a checker may use only an event control for
  // timing; a delay control is rejected. The event-controlled form of the same
  // initial elaborates cleanly
  // (CheckerInitialProcedureAdmitsEventControlTiming), isolating the delay as
  // the cause.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk;\n"
      "  logic ok;\n"
      "  initial #5 ok = 1'b1;\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
