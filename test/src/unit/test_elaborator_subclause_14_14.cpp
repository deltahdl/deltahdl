#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(GlobalClockingElab, DuplicateGlobalClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  global clocking gc1 @(posedge clk1); endclocking\n"
      "  global clocking gc2 @(posedge clk2); endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only one global clocking block is allowed per "
                            "scope",
                            3, "14.14"));
}

TEST(GlobalClockingElab, GlobalClockInEventControlWithoutDeclarationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  always @($global_clock) x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            3, "14.14"));
}

TEST(GlobalClockingElab, GlobalClockInEventControlWithDeclarationIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, x;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  always @($global_clock) x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §14.14 lookup rule b): a $global_clock reference in a child that declares no
// global clocking of its own resolves against the parent instance's global
// clocking. This is the common_sub pattern from the clause example.
//
// This case and the next assert acceptance, which is all elaboration can say
// about them: a process that arms no watcher and stays suspended at
// @($global_clock) for the whole run is accepted too. What the reference
// resolves to is asserted by GlobalClockInAChildFollowsItsAncestorsDeclaration
// and SiblingInstancesEachFollowTheirOwnAncestorsDeclaration in
// test/src/unit/test_simulator_subclause_14_14.cpp, which drive the declared
// clock and read back what the child's process wrote.
TEST(GlobalClockingElab, GlobalClockResolvesToParentInstanceDeclaration) {
  ElabFixture f;
  ElaborateSrc(
      "module child;\n"
      "  logic x;\n"
      "  always @($global_clock) x = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk;\n"
      "  global clocking gc @(posedge clk); endclocking\n"
      "  child c();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §14.14 rule b) climbs through more than one level of instantiation until a
// global clocking is found.
TEST(GlobalClockingElab, GlobalClockResolvesThroughTwoInstanceLevels) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf;\n"
      "  logic x;\n"
      "  always @($global_clock) x = 1'b1;\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf l();\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk;\n"
      "  global clocking gc @(posedge clk); endclocking\n"
      "  mid m();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §14.14 rule b) error path: when the lookup reaches the top-level hierarchy
// block without finding a global clocking, the reference is an error even
// though it sits several levels below the top.
TEST(GlobalClockingElab,
     GlobalClockWithNoDeclarationAnywhereInHierarchyErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf;\n"
      "  logic x;\n"
      "  always @($global_clock) x = 1'b1;\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf l();\n"
      "endmodule\n"
      "module top;\n"
      "  mid m();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            3, "14.14"));
}

// §14.14: the at-most-one-per-scope rule applies to every scope kind the clause
// enumerates, not just modules -- here two global clockings in one interface.
TEST(GlobalClockingElab, DuplicateGlobalClockingInInterfaceErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  logic clk1, clk2;\n"
      "  global clocking gc1 @(posedge clk1); endclocking\n"
      "  global clocking gc2 @(posedge clk2); endclocking\n"
      "endinterface\n"
      "module top;\n"
      "  ifc i();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only one global clocking block is allowed per "
                            "scope",
                            4, "14.14"));
}

// §14.14: the at-most-one rule also holds in a program scope. The program is
// named as the explicit top so its body is actually elaborated.
TEST(GlobalClockingElab, DuplicateGlobalClockingInProgramErrors) {
  ElabFixture f;
  ElaborateSrc(
      "program p(input clk1, input clk2);\n"
      "  global clocking gc1 @(posedge clk1); endclocking\n"
      "  global clocking gc2 @(posedge clk2); endclocking\n"
      "endprogram\n",
      f, "p");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only one global clocking block is allowed per "
                            "scope",
                            3, "14.14"));
}

// §14.14: and in a checker scope -- the fourth declared scope the clause
// enumerates. The checker is named as the explicit top so it is elaborated.
TEST(GlobalClockingElab, DuplicateGlobalClockingInCheckerErrors) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input clk1, input clk2);\n"
      "  global clocking gc1 @(posedge clk1); endclocking\n"
      "  global clocking gc2 @(posedge clk2); endclocking\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only one global clocking block is allowed per "
                            "scope",
                            3, "14.14"));
}

// §14.14: the report that refuses a second global clocking declaration names
// the subclause stating the rule ("A given module, interface, checker, or
// program shall contain at most one global clocking declaration").
TEST(GlobalClockingElab, DuplicateGlobalClockingNames14_14) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  global clocking gc1 @(posedge clk1); endclocking\n"
      "  global clocking gc2 @(posedge clk2); endclocking\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only one global clocking block is allowed per scope", 3, "14.14"));
}

// The body statement of the one process each of the two instances the top
// module holds was elaborated into. The two cases below differ in the source
// they elaborate and in what they claim about the pair, so the walk from the
// design down to the two RtlirProcess::body pointers is written once here.
void InstanceProcessBodies(RtlirDesign* design, Stmt** first, Stmt** second) {
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 2U);
  auto* u0 = top->children[0].resolved;
  auto* u1 = top->children[1].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_NE(u1, nullptr);
  ASSERT_EQ(u0->processes.size(), 1U);
  ASSERT_EQ(u1->processes.size(), 1U);
  *first = u0->processes[0].body;
  *second = u1->processes[0].body;
}

// §14.14: an event control naming $global_clock waits on the event expression
// of the effective global clocking declaration, so BuildProcessBody in
// src/elaborator/elaborator_process.cpp rewrites the event control the
// procedure body holds. The body it rewrites is reached through the one
// ModuleDecl the parser built, and Elaborator::ElaborateModule runs once per
// instantiation, so a rewrite made in place is written into the statement
// every instance of the module shares. This fails when the two instances of
// `sub` name one Stmt.
TEST(GlobalClockingElab,
     GlobalClockSubstitutionGivesEachInstanceItsOwnProcessBody) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub;\n"
      "  logic clk, done;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  initial @($global_clock) done = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  sub u0();\n"
      "  sub u1();\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(f.has_errors);
  Stmt* first = nullptr;
  Stmt* second = nullptr;
  InstanceProcessBodies(design, &first, &second);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_NE(first, second)
      << "both instances of sub hold one body statement, so the §14.14 "
         "substitution made for either of them was written into the other";
}

// §14.14: a procedure body naming no $global_clock has nothing to substitute,
// so SubstituteGlobalClockEventControls in
// src/elaborator/global_clock_assertion_event.cpp returns the statement it was
// given rather than a copy of it. Both instances of `sub` then hold the one
// Stmt the parser built for the module, which is what the elaborator does with
// every process body it does not rewrite. This fails when a body is copied per
// instance whether anything in it was rewritten or not.
TEST(GlobalClockingElab, ProcessBodyWithNoGlobalClockIsSharedBetweenInstances) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub;\n"
      "  logic clk, done;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  initial done = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  sub u0();\n"
      "  sub u1();\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(f.has_errors);
  Stmt* first = nullptr;
  Stmt* second = nullptr;
  InstanceProcessBodies(design, &first, &second);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(first, second)
      << "a body naming no $global_clock was copied per instance, so every "
         "process body is allocated again for every instantiation";
}

// §14.14 ends both of its lookup rules "the lookup terminates and shall result
// in an error", and states no condition on where the reference stands, so a
// $global_clock written in any statement position of a module that declares no
// global clocking and is instantiated under none is an error. The seven cases
// below each put the reference in one such position, and each is a position
// Elaborator::ValidateGlobalClockReference reached only once its search took
// its list of nested statements from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. Every one of them elaborated
// clean beforehand, and an event control among them then armed no watcher and
// suspended its process for the whole run.

// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword ...`, so a fork
// holds statements the way a begin-end block does. The parser keeps them in
// Stmt::fork_stmts rather than in Stmt::stmts.
TEST(GlobalClockingElab, GlobalClockInAForkStatementWithoutDeclarationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial fork\n"
      "    @($global_clock) x = 1'b1;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            4, "14.14"));
}

// A.6.8's for_initialization is a list of variable assignments, so the loop
// header holds statements of its own in Stmt::for_inits and an expression
// written there is an expression of the design like any other.
TEST(GlobalClockingElab, GlobalClockInAForInitializerWithoutDeclarationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = $global_clock; i < 1; i = i + 1)\n"
      "      x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            5, "14.14"));
}

// A.6.8's for_step_assignment is the same rule at the other end of the loop
// header, kept in Stmt::for_steps. The initializer here assigns a constant, so
// the reference the report names can only be the one in the step.
TEST(GlobalClockingElab, GlobalClockInAForStepWithoutDeclarationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; i = $global_clock)\n"
      "      x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            5, "14.14"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. The two cases
// below cover one arm each.
TEST(GlobalClockingElab,
     GlobalClockInAnAssertionPassStatementWithoutDeclarationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x, ok;\n"
      "  initial assert (ok) @($global_clock) x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            3, "14.14"));
}

TEST(GlobalClockingElab,
     GlobalClockInAnAssertionFailStatementWithoutDeclarationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x, ok;\n"
      "  initial assert (ok) else @($global_clock) x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            3, "14.14"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. The rule
// is a static one, so it holds whether the weighted draw would select the item
// or not.
TEST(GlobalClockingElab, GlobalClockInARandcaseItemWithoutDeclarationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial randcase 1: @($global_clock) x = 1'b1; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            3, "14.14"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions.
TEST(GlobalClockingElab,
     GlobalClockInARandsequenceCodeBlockWithoutDeclarationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { @($global_clock) x = 1'b1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            5, "14.14"));
}

// A.6.5 gives an event control two expressions -- `[ edge_identifier ]
// expression [ iff expression ]` -- and §14.14 states no condition on which of
// them $global_clock is written in. An always procedure keeps its event list in
// ModuleItem::sensitivity, and the walk over that list read the signal alone,
// so this source elaborated clean while the procedural form of it was reported.
TEST(GlobalClockingElab, GlobalClockInAnAlwaysIffConditionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic x;\n"
      "  always @(posedge clk iff $global_clock) x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration",
                            4, "14.14"));
}

}  // namespace
