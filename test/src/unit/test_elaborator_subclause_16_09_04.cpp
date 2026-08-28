#include <gtest/gtest.h>

#include "elaborator/global_clocking_sampled_value.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §16.9.4: the provided functions are the past functions $past_gclk,
// $rose_gclk, $fell_gclk, $stable_gclk, $changed_gclk and the future functions
// $future_gclk, $rising_gclk, $falling_gclk, $steady_gclk, $changing_gclk.
TEST(GlobalClockingSampledFunctions, RecognizesEveryProvidedFunction) {
  GlobalClockingSampledFunction fn{};
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$past_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kPastGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$rose_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kRoseGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$fell_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kFellGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$stable_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kStableGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$changed_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kChangedGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$future_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kFutureGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$rising_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kRisingGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$falling_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kFallingGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$steady_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kSteadyGclk);
  EXPECT_TRUE(ClassifyGlobalClockingSampledFunction("$changing_gclk", fn));
  EXPECT_EQ(fn, GlobalClockingSampledFunction::kChangingGclk);
}

// §16.9.4: a name that is not a global clocking sampled value function is not
// classified (e.g. the ordinary $past).
TEST(GlobalClockingSampledFunctions, RejectsNonGclkNames) {
  EXPECT_FALSE(IsGlobalClockingSampledFunction("$past"));
  EXPECT_FALSE(IsGlobalClockingSampledFunction("$rose"));
}

// §16.9.4: the past functions and future functions are partitioned by whether
// they use a past or a subsequent sampled value.
TEST(GlobalClockingSampledFunctions, PartitionsPastAndFuture) {
  EXPECT_TRUE(
      IsGlobalClockingPastFunction(GlobalClockingSampledFunction::kRoseGclk));
  EXPECT_FALSE(
      IsGlobalClockingFutureFunction(GlobalClockingSampledFunction::kRoseGclk));
  EXPECT_TRUE(IsGlobalClockingFutureFunction(
      GlobalClockingSampledFunction::kRisingGclk));
  EXPECT_FALSE(
      IsGlobalClockingPastFunction(GlobalClockingSampledFunction::kRisingGclk));
}

// §16.9.4: the future functions may be invoked only in a property_expr or a
// sequence_expr; in particular not in an action block.
TEST(GlobalClockingSampledFunctions, FutureFunctionsLimitedToAssertionExprs) {
  EXPECT_TRUE(GlobalClockingFutureFunctionAllowedIn(
      GlobalClockingFunctionPlace::kPropertyExpr));
  EXPECT_TRUE(GlobalClockingFutureFunctionAllowedIn(
      GlobalClockingFunctionPlace::kSequenceExpr));
  EXPECT_FALSE(GlobalClockingFutureFunctionAllowedIn(
      GlobalClockingFunctionPlace::kActionBlock));
  EXPECT_FALSE(GlobalClockingFutureFunctionAllowedIn(
      GlobalClockingFunctionPlace::kProceduralCode));
}

// §16.9.4: the past functions are usable everywhere the ordinary sampled value
// functions are, including action blocks and general procedural code.
TEST(GlobalClockingSampledFunctions, PastFunctionsUsableInActionBlocks) {
  EXPECT_TRUE(GlobalClockingPastFunctionAllowedIn(
      GlobalClockingFunctionPlace::kActionBlock));
  EXPECT_TRUE(GlobalClockingPastFunctionAllowedIn(
      GlobalClockingFunctionPlace::kProceduralCode));
}

// §16.9.4: the future functions shall not be nested.
TEST(GlobalClockingSampledFunctions, FutureFunctionsMayNotNest) {
  EXPECT_TRUE(GlobalClockingFutureFunctionNestingAllowed(false));
  EXPECT_FALSE(GlobalClockingFutureFunctionNestingAllowed(true));
}

// §16.9.4: the future functions shall not be used in assertions containing
// sequence match items.
TEST(GlobalClockingSampledFunctions, FutureFunctionsRejectSequenceMatchItems) {
  EXPECT_TRUE(GlobalClockingFutureFunctionAllowedWithSequenceMatchItems(false));
  EXPECT_FALSE(GlobalClockingFutureFunctionAllowedWithSequenceMatchItems(true));
}

// §16.9.4: the global clocking sampled value functions may be used only if a
// global clocking is defined. A past function used in procedural code without
// any global clocking declaration in scope is rejected during elaboration.
TEST(GlobalClockingElab, GclkFunctionWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x;\n"
      "  always @(posedge clk) x = $past_gclk(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "clocking declaration in an enclosing scope", 4,
                            "16.9.4"));
}

// §16.9.4: with a global clocking declared in scope, the same past-function use
// in procedural code is accepted (the past functions are usable in general
// procedural code).
TEST(GlobalClockingElab, GclkFunctionWithGlobalClockingIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  always @(posedge clk) x = $past_gclk(x);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §16.9.4: the future functions may be invoked only in a property or sequence
// expression, so a future function in ordinary procedural code is rejected —
// even when a global clocking is defined (which isolates this from the
// requires-global-clocking rule). A past function in the same position is legal
// (see GclkFunctionWithGlobalClockingIsAccepted).
TEST(GlobalClockingElab, FutureFunctionInProceduralCodeErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x, y;\n"
      "  global clocking gc @(posedge clk); endclocking\n"
      "  always @(posedge clk) x = $future_gclk(y);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only in a property or sequence expression", 5,
                            "16.9.4"));
}

// §16.9.4: "global clocking is defined" is resolved with the §14.14 scope
// rules, so the declaration need not be in the same module. A child instance
// that uses a past function but declares no global clocking of its own is
// accepted when an enclosing instance supplies one (§14.14 lookup rule b).
TEST(GlobalClockingElab, GclkFunctionResolvesGlobalClockingFromParentInstance) {
  ElabFixture f;
  ElaborateSrc(
      "module child;\n"
      "  logic clk;\n"
      "  logic [31:0] x;\n"
      "  always @(posedge clk) x = $past_gclk(x);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk;\n"
      "  global clocking gc @(posedge clk); endclocking\n"
      "  child c();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §16.9.4 says the global clocking sampled value functions "may be used only
// if global clocking is defined (see 14.14)" and states no condition on where
// the call stands, so a $past_gclk written in any statement position of a
// module that declares no global clocking and is instantiated under none is an
// error. §16.9.4 also says "the global clocking past sampled value functions
// are usable in general procedural code and action blocks", so every case below
// breaks the requires-a-declaration rule alone and the placement rule the
// future functions carry cannot account for the report.
//
// The seven cases each put the call in one statement position, and each is a
// position Elaborator::ValidateGclkRequiresGlobalClocking reached only once
// FindGclkFunctionRefInSubStmts in
// src/elaborator/elaborator_validate_global_clocking.cpp took its list of
// nested statements from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. Every one of them elaborated
// clean beforehand, with the design left to sample a global clock it has no
// declaration for.

// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword ...`, so a fork
// holds statements the way a begin-end block does. The parser keeps them in
// Stmt::fork_stmts rather than in Stmt::stmts.
TEST(GlobalClockingElab,
     GclkFunctionInAForkStatementWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial fork\n"
      "    x = $past_gclk(x);\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 4,
      "16.9.4"));
}

// A.6.8's for_initialization is a list of variable assignments, so the loop
// header holds statements of its own in Stmt::for_inits and a call written
// there is a use of the function like any other.
TEST(GlobalClockingElab,
     GclkFunctionInAForInitializerWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = $past_gclk(x); i < 1; i = i + 1)\n"
      "      x = 32'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 5,
      "16.9.4"));
}

// A.6.8's for_step_assignment is the same rule at the other end of the loop
// header, kept in Stmt::for_steps. The initializer here assigns a constant, so
// the call the report names can only be the one in the step.
TEST(GlobalClockingElab, GclkFunctionInAForStepWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; i = $past_gclk(x))\n"
      "      x = 32'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 5,
      "16.9.4"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. The two cases
// below cover one arm each.
TEST(GlobalClockingElab,
     GclkFunctionInAnAssertionPassStatementWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  logic ok;\n"
      "  initial assert (ok) x = $past_gclk(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 4,
      "16.9.4"));
}

TEST(GlobalClockingElab,
     GclkFunctionInAnAssertionFailStatementWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  logic ok;\n"
      "  initial assert (ok) else x = $past_gclk(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 4,
      "16.9.4"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. The rule
// is a static one, so it holds whether the weighted draw would select the item
// or not.
TEST(GlobalClockingElab,
     GclkFunctionInARandcaseItemWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial randcase 1: x = $past_gclk(x); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 3,
      "16.9.4"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions.
TEST(GlobalClockingElab,
     GclkFunctionInARandsequenceCodeBlockWithoutGlobalClockingErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = $past_gclk(x); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "requires a global clocking declaration in an enclosing scope", 5,
      "16.9.4"));
}

}  // namespace
