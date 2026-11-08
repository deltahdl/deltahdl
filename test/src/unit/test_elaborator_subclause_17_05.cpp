#include <gtest/gtest.h>

#include "elaborator/checker_procedures.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CheckerProcedures, OnlyInitialAlwaysAndFinalProceduresAreAllowed) {
  EXPECT_TRUE(ProceduralBlockAllowedInChecker(ProceduralBlockKind::kInitial));
  EXPECT_TRUE(ProceduralBlockAllowedInChecker(ProceduralBlockKind::kFinal));
}

TEST(CheckerProcedures, InitialProcedureMayContainItsListedConstructs) {
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
  EXPECT_TRUE(CheckerInitialProcedureAllows(
      CheckerInitialContent::kEventTimingControl));
  EXPECT_FALSE(CheckerInitialProcedureAllows(
      CheckerInitialContent::kDelayTimingControl));
  EXPECT_FALSE(
      CheckerInitialProcedureAllows(CheckerInitialContent::kWaitTimingControl));
}

TEST(CheckerProcedures, BlockingAssignmentLimitedToCombAndLatch) {
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
  EXPECT_TRUE(CheckerAlwaysExpressionIsSampled(
      CheckerAlwaysForm::kAlwaysFf, CheckerAlwaysExpressionPosition::kBody));
  EXPECT_FALSE(CheckerAlwaysExpressionIsSampled(
      CheckerAlwaysForm::kAlwaysFf,
      CheckerAlwaysExpressionPosition::kEventControl));
}

TEST(CheckerProcedures, CombAndLatchExpressionsAreNotImplicitlySampled) {
  for (auto pos : {CheckerAlwaysExpressionPosition::kBody,
                   CheckerAlwaysExpressionPosition::kEventControl}) {
    EXPECT_FALSE(
        CheckerAlwaysExpressionIsSampled(CheckerAlwaysForm::kAlwaysComb, pos));
    EXPECT_FALSE(
        CheckerAlwaysExpressionIsSampled(CheckerAlwaysForm::kAlwaysLatch, pos));
  }
}

TEST(CheckerProcedures, ClockInferenceDefersToTheSharedInferenceRules) {
  EXPECT_TRUE(CheckerProcedureClockInferenceFollowsProceduralAssertionRules());
}

TEST(CheckerProcedures, FinalProcedureMatchesModuleSemantics) {
  EXPECT_TRUE(CheckerFinalProcedureIsAllowed());
  EXPECT_TRUE(CheckerFinalProcedureRunsOncePerInstantiation());
  EXPECT_FALSE(CheckerFinalProceduresHaveImpliedOrdering());
  EXPECT_FALSE(CheckerFinalProcedureDependsOnInstantiationContext());
}

TEST(CheckerProcedures, GeneralAlwaysInCheckerBodyIsRejectedInElaboration) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic clk, input logic d);\n"
      "  logic q;\n"
      "  always @(posedge clk) q <= d;\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a general 'always' procedure cannot be used inside checker", 3, "17.5"));
}

TEST(CheckerProcedures, SpecializedAlwaysFormsInCheckerBodyElaborateCleanly) {
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

TEST(CheckerProcedures, CheckerFinalRejectsConstructsAModuleFinalRejects) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk;\n"
      "  final #5 $display(\"late\");\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "final procedure shall not contain timing controls",
                            2, "9.2.3"));
}

TEST(CheckerProcedures, CheckerFinalAdmitsWhatAModuleFinalAdmits) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk;\n"
      "  final $display(\"done\");\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerProcedures, CheckerInitialProcedureElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk;\n"
      "  logic ok = 1'b0;\n"
      "  initial a0: assert (ok == 1'b0);\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerProcedures, CheckerInitialProcedureAdmitsEventControlTiming) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic clk);\n"
      "  initial @(posedge clk) a0: assert (clk);\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerProcedures, CheckerAlwaysProcedureAdmitsCaseSelection) {
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

TEST(CheckerProcedures, BlockingAssignmentInCheckerAlwaysFfIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic clk, input logic d);\n"
      "  logic q;\n"
      "  always_ff @(posedge clk) q = d;\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a blocking assignment cannot appear in an "
                            "always_ff procedure of checker",
                            3, "17.7.1"));
}

TEST(CheckerProcedures, CheckerInitialProcedureRejectsDelayTimingControl) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk;\n"
      "  logic ok;\n"
      "  initial #5 ok = 1'b1;\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "may use only an event control for timing; a delay, a cycle delay and a "
      "wait are not allowed",
      3, "17.5"));
}

TEST(CheckerProcedures,
     BlockingAssignmentInAlwaysFfAssertionPassActionIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic clk, input logic d);\n"
      "  logic q;\n"
      "  always_ff @(posedge clk) assert (d) q = d;\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a blocking assignment cannot appear in an "
                            "always_ff procedure of checker",
                            3, "17.7.1"));
}

TEST(CheckerProcedures,
     BlockingAssignmentInAlwaysFfAssertionFailActionIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic clk, input logic d);\n"
      "  logic q;\n"
      "  always_ff @(posedge clk) assert (d) q <= d; else q = d;\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a blocking assignment cannot appear in an "
                            "always_ff procedure of checker",
                            3, "17.7.1"));
}

TEST(CheckerProcedures,
     ForLoopHeaderInCheckerAlwaysFfIsNotABlockingAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic clk, input logic [3:0] d);\n"
      "  logic q;\n"
      "  always_ff @(posedge clk)\n"
      "    for (int i = 0; i < 4; i = i + 1) q <= d[i];\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerProcedures, DelayInCheckerInitialAssertionPassActionIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic d);\n"
      "  initial assert (d) #5 $display(\"late\");\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "may use only an event control for timing; a delay, a cycle delay and a "
      "wait are not allowed",
      2, "17.5"));
}

TEST(CheckerProcedures, DelayInCheckerInitialAssertionFailActionIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic d);\n"
      "  initial assert (d) $display(\"ok\"); else #5 $display(\"late\");\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "may use only an event control for timing; a delay, a cycle delay and a "
      "wait are not allowed",
      2, "17.5"));
}

TEST(CheckerProcedures, AnInitialStatementOffTheListIsReported) {
  const char* const kReport =
      "this statement is none of those an initial procedure of checker 'chk' "
      "may hold";
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a);\n"
      "  initial begin\n"
      "    if (a) a0: assert (a);\n"
      "    $display(\"x\");\n"
      "    a1: assert (a) else $display(\"bad\");\n"
      "    m1: assume (a) else $display(\"bad\");\n"
      "    c1: cover (a) $display(\"hit\");\n"
      "  end\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 3, "17.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 4, "17.5"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 5, "17.5"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 6, "17.5"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 7, "17.5"));
}

TEST(CheckerProcedures, AnAlwaysStatementOffTheListIsReported) {
  const char* const kReport =
      "this statement is none of those an always procedure of checker 'chk' "
      "may hold";
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk, a);\n"
      "  bit q;\n"
      "  always_ff @(posedge clk) begin\n"
      "    fork\n"
      "      q <= a;\n"
      "    join\n"
      "    if (a) q <= 1'b0;\n"
      "  end\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 4, "17.5"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 7, "17.5"));
}

}  // namespace
