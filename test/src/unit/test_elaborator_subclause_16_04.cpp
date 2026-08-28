#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DeferredAssertionElaboration, SingleSystemTaskPassActionAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial assert #0 (c) $info(\"ok\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DeferredAssertionElaboration, UserTaskCallPassActionAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task do_pass; endtask\n"
      "  logic c;\n"
      "  initial assert #0 (c) do_pass();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.4: a deferred assertion action block may contain a single subroutine
// call; a void function call is one of the permitted call forms (alongside a
// task, task method, void function method, and system task), so it is accepted
// with no single-call diagnostic, just like the task and system-task forms.
TEST(DeferredAssertionElaboration, VoidFunctionCallActionAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  function void note; endfunction\n"
      "  logic c;\n"
      "  initial assert #0 (c) note();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DeferredAssertionElaboration, OmittedActionsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial begin\n"
      "    assert #0 (c);\n"
      "    cover final (c);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.4: "The pass and fail statements in a deferred assertion's action_block,
// if present, shall each consist of a single subroutine call. ... The
// requirement of a single subroutine call implies that no begin-end block shall
// surround the pass or fail statements, as begin is itself a statement that is
// not a subroutine call." §1.5 defines shall as a mandatory requirement "from
// which no deviation is permitted", so each of the forms below is illegal
// source and elaboration rejects it rather than reporting it and carrying on.
TEST(DeferredAssertionElaboration, BeginEndPassBlockRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial assert #0 (c) begin $info(\"a\"); $info(\"b\"); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "deferred assertion pass action shall be a single "
                            "subroutine call",
                            3, "16.4"));
}

TEST(DeferredAssertionElaboration, BeginEndFailBlockRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial assert #0 (c) else begin $error(\"x\"); $error(\"y\"); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "deferred assertion fail action shall be a single "
                            "subroutine call",
                            3, "16.4"));
}

TEST(DeferredAssertionElaboration, AssignmentInPassActionRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  logic [7:0] x;\n"
      "  initial assert #0 (c) x = 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "deferred assertion pass action shall be a single "
                            "subroutine call",
                            4, "16.4"));
}

// §16.3 gives the opposite rule for a simple immediate assertion: "the fail
// statement, like the pass statement, is any legal SystemVerilog procedural
// statement". The same begin-end block that §16.4 rejects above is therefore
// legal without the #0, and this pair pins that the rejection follows the
// deferral rather than the block.
TEST(DeferredAssertionElaboration, NonDeferredBeginEndAccepted) {
  ElabFixture deferred;
  ASSERT_NE(
      Elaborate(
          "module m;\n"
          "  logic c;\n"
          "  initial assert #0 (c) begin $info(\"a\"); $info(\"b\"); end\n"
          "endmodule\n",
          deferred),
      nullptr);
  ASSERT_TRUE(ReportedError(deferred.diag.Diagnostics(),
                            "deferred assertion pass action shall be a single "
                            "subroutine call",
                            3, "16.4"));

  ElabFixture plain;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial assert(c) begin $info(\"a\"); $info(\"b\"); end\n"
      "endmodule\n",
      plain);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(plain.has_errors);
}

TEST(DeferredAssertionElaboration, DeferredAssumeBeginEndRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial assume #0 (c) begin $info(\"a\"); $info(\"b\"); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "deferred assertion pass action shall be a single "
                            "subroutine call",
                            3, "16.4"));
}

TEST(DeferredAssertionElaboration, DeferredCoverBeginEndRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  initial cover #0 (c) begin $info(\"a\"); $info(\"b\"); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "deferred assertion pass action shall be a single "
                            "subroutine call",
                            3, "16.4"));
}

TEST(DeferredAssertionElaboration, FinalDeferredPostponedIllegalCalleeFlagged) {
  ElabFixture deferred_final;
  ASSERT_NE(Elaborate("module m;\n"
                      "  logic [7:0] x;\n"
                      "  task mutator; x = 8'd1; endtask\n"
                      "  initial assert final (1) mutator();\n"
                      "endmodule\n",
                      deferred_final),
            nullptr);
  uint32_t final_warnings = deferred_final.diag.WarningCount();
  ASSERT_GE(final_warnings, 1u);

  ElabFixture deferred_obs;
  ASSERT_NE(Elaborate("module m;\n"
                      "  logic [7:0] x;\n"
                      "  task mutator; x = 8'd1; endtask\n"
                      "  initial assert #0 (1) mutator();\n"
                      "endmodule\n",
                      deferred_obs),
            nullptr);
  EXPECT_LT(deferred_obs.diag.WarningCount(), final_warnings);
}

TEST(DeferredAssertionElaboration, FinalDeferredPostponedSafeCalleeAccepted) {
  ElabFixture safe;
  ASSERT_NE(Elaborate("module m;\n"
                      "  task reporter; $info(\"ok\"); endtask\n"
                      "  initial assert final (1) reporter();\n"
                      "endmodule\n",
                      safe),
            nullptr);
  ElabFixture unsafe;
  ASSERT_NE(Elaborate("module m;\n"
                      "  logic [7:0] x;\n"
                      "  task mutator; x = 8'd1; endtask\n"
                      "  initial assert final (1) mutator();\n"
                      "endmodule\n",
                      unsafe),
            nullptr);
  EXPECT_LT(safe.diag.WarningCount(), unsafe.diag.WarningCount());
}

TEST(DeferredAssertionElaboration, ClassMemberToRefFormalRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  class C; int v; endclass\n"
      "  C h = new();\n"
      "  task by_ref(ref int r); endtask\n"
      "  initial assert #0 (1) by_ref(h.v);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot pass dynamic variable as actual for ref "
                            "formal 'r' in deferred-assertion call",
                            5, "16.4"));
}

TEST(DeferredAssertionElaboration, StaticVarToRefFormalAccepted) {
  ElabFixture f;
  // §13.5.2: pass-by-reference is illegal for a subroutine with static
  // lifetime, so the task must be automatic for the ref formal to be legal; a
  // static variable is then accepted as the ref actual.
  auto* design = Elaborate(
      "module m;\n"
      "  int s;\n"
      "  task automatic by_ref(ref int r); endtask\n"
      "  initial assert #0 (1) by_ref(s);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.4: it shall be an error to pass a dynamic variable as the actual for a
// const ref formal too, not only a plain ref formal -- the restriction is on
// the pass-by-reference direction regardless of constness. A class property
// (dynamic storage) passed to a `const ref` formal is rejected.
TEST(DeferredAssertionElaboration, ClassMemberToConstRefFormalRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  class C; int v; endclass\n"
      "  C h = new();\n"
      "  task by_cref(const ref int r); endtask\n"
      "  initial assert #0 (1) by_cref(h.v);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot pass dynamic variable as actual for ref "
                            "const formal 'r' in deferred-assertion call",
                            5, "16.4"));
}

// §16.4: it shall be an error to pass an automatic variable as the actual for a
// ref formal of a deferred-assertion action call. A local of an automatic task
// has automatic storage, so passing it by reference is rejected.
TEST(DeferredAssertionElaboration, AutomaticLocalToRefFormalRejected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task automatic caller;\n"
      "    int loc;\n"
      "    assert #0 (1) upd(loc);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot pass automatic variable as actual for ref "
                            "formal 'r' in deferred-assertion call",
                            5, "16.4"));
}

// §16.4: the automatic-variable restriction is on the variable's storage, not
// on the enclosing subroutine's lifetime. A module-level static variable passed
// by reference is accepted even from inside an automatic task, so the check
// does not over-reject.
TEST(DeferredAssertionElaboration,
     StaticVarFromAutomaticTaskToRefFormalAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int s;\n"
      "  task automatic use_static(ref int r); endtask\n"
      "  task automatic caller;\n"
      "    assert #0 (1) use_static(s);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.4: the report that refuses an action block which is not a single
// subroutine call names the subclause stating the rule, and states it once.
// The sentence opened with "§16.4:" until the field carried it, and
// DiagEngine::Emit appends the field, so a message that still held the sign
// would print the subclause twice.
TEST(DeferredAssertionElaboration, AssignmentPassActionNames16_4) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic c;\n"
      "  logic [7:0] x;\n"
      "  initial assert #0 (c) x = 8'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "deferred assertion pass action shall be a single",
                            4, "16.4"));
  for (const auto& reported : f.diag.Diagnostics()) {
    EXPECT_EQ(reported.message.find("§"), std::string::npos);
  }
}

// §16.4 refuses a final deferred assertion whose callee body holds a statement
// the Postponed region cannot run, and it names no statement position the
// restriction is suspended in. The seven cases below write the offending
// assignment in each of the seven links ContainsPostponedIllegalStmt in
// src/elaborator/elaborator_validate_assertion_actions.cpp did not descend
// before it was handed the list ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states, so each one saw the
// callee as legal in the Postponed region and made no report.

// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword`, so a fork arm
// holds an ordinary blocking assignment.
TEST(DeferredAssertionElaboration,
     FinalDeferredCalleeAssignsInAForkArmFlagged) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task mutator;\n"
      "    fork\n"
      "      x = 8'd1;\n"
      "    join\n"
      "  endtask\n"
      "  initial assert final (1) mutator();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "whose body contains statements not legally "
                              "callable in the Postponed region",
                              8, "16.4"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...`, so
// the loop header's first clause is an assignment like any other. The step
// clause is left empty here, which leaves the initialization as the only
// assignment in the callee.
TEST(DeferredAssertionElaboration,
     FinalDeferredCalleeAssignsInAForInitializationFlagged) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task mutator;\n"
      "    for (x = 8'd0; 1'b0; ) ;\n"
      "  endtask\n"
      "  initial assert final (1) mutator();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "whose body contains statements not legally "
                              "callable in the Postponed region",
                              6, "16.4"));
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, so an assignment stands in
// the step clause too. The initialization clause is left empty here, which
// leaves the step as the only assignment in the callee.
TEST(DeferredAssertionElaboration,
     FinalDeferredCalleeAssignsInAForStepFlagged) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task mutator;\n"
      "    for ( ; 1'b0; x = 8'd1) ;\n"
      "  endtask\n"
      "  initial assert final (1) mutator();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "whose body contains statements not legally "
                              "callable in the Postponed region",
                              6, "16.4"));
}

// A.6.10 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so either arm of an immediate assertion inside the callee
// holds an assignment. The assertion here is not deferred, so §16.4's
// single-subroutine-call rule does not apply to it and the assignment is legal
// where it stands.
TEST(DeferredAssertionElaboration,
     FinalDeferredCalleeAssignsInAnAssertionPassActionFlagged) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task mutator;\n"
      "    assert (1'b1) x = 8'd1;\n"
      "  endtask\n"
      "  initial assert final (1) mutator();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "whose body contains statements not legally "
                              "callable in the Postponed region",
                              6, "16.4"));
}

TEST(DeferredAssertionElaboration,
     FinalDeferredCalleeAssignsInAnAssertionFailActionFlagged) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task mutator;\n"
      "    assert (1'b1) else x = 8'd1;\n"
      "  endtask\n"
      "  initial assert final (1) mutator();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "whose body contains statements not legally "
                              "callable in the Postponed region",
                              6, "16.4"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase arm holds the assignment directly. §16.4 is a rule about what the
// callee's body can be asked to run, so it holds whether the weighted draw
// would select the arm or not.
TEST(DeferredAssertionElaboration,
     FinalDeferredCalleeAssignsInARandcaseArmFlagged) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task mutator;\n"
      "    randcase\n"
      "      1 : x = 8'd1;\n"
      "    endcase\n"
      "  endtask\n"
      "  initial assert final (1) mutator();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "whose body contains statements not legally "
                              "callable in the Postponed region",
                              8, "16.4"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds the assignment.
TEST(DeferredAssertionElaboration,
     FinalDeferredCalleeAssignsInARandsequenceCodeBlockFlagged) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task mutator;\n"
      "    randsequence(main)\n"
      "      main : { x = 8'd1; };\n"
      "    endsequence\n"
      "  endtask\n"
      "  initial assert final (1) mutator();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "whose body contains statements not legally "
                              "callable in the Postponed region",
                              8, "16.4"));
}

// §16.4 bars an automatic variable as the actual for a pass-by-reference formal
// of a deferred-assertion action call. Two walks in
// src/elaborator/elaborator_validate_assertion_actions.cpp answer that
// together: CollectAutomaticVarNames gathers the names an enclosing routine
// declares automatic, and Elaborator::WalkStmtsForDeferredActions finds the
// deferred assertion whose call passes one of them. Each wrote its own list of
// the statement links to descend, and each omitted the same five, so the cases
// below put the declaration and the deferred assertion in those links.
//
// A.6.8 admits in a for_initialization only a list_of_variable_assignments or a
// for_variable_declaration, and in a for_step_assignment only an
// operator_assignment, an inc_or_dec_expression or a function_subroutine_call.
// No statement stands in either, so a deferred assertion cannot be written
// there, and the parser records a for-header declaration as an assignment in
// Stmt::for_inits rather than as a Stmt of kind kVarDecl, so no declaration is
// collected there either. Those two links therefore take no case.

// The deferred assertion in a fork arm, with the automatic declared at the top
// of the enclosing automatic task, so the report turns on
// Elaborator::WalkStmtsForDeferredActions reaching Stmt::fork_stmts.
TEST(DeferredAssertionElaboration,
     AutomaticLocalToRefFormalInAForkArmRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task automatic caller;\n"
      "    int loc;\n"
      "    fork\n"
      "      assert #0 (1) upd(loc);\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot pass automatic variable as actual for ref "
                            "formal 'r' in deferred-assertion call",
                            6, "16.4"));
}

TEST(DeferredAssertionElaboration,
     AutomaticLocalToRefFormalInARandcaseArmRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task automatic caller;\n"
      "    int loc;\n"
      "    randcase\n"
      "      1 : assert #0 (1) upd(loc);\n"
      "    endcase\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot pass automatic variable as actual for ref "
                            "formal 'r' in deferred-assertion call",
                            6, "16.4"));
}

TEST(DeferredAssertionElaboration,
     AutomaticLocalToRefFormalInARandsequenceCodeBlockRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task automatic caller;\n"
      "    int loc;\n"
      "    randsequence(main)\n"
      "      main : { assert #0 (1) upd(loc); };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot pass automatic variable as actual for ref "
                            "formal 'r' in deferred-assertion call",
                            6, "16.4"));
}

// The three pairs below turn on CollectAutomaticVarNames instead. §6.21 makes a
// local of a static task static unless it is declared automatic, so each pair
// writes the same source twice inside a static task and varies only the
// lifetime keyword on the declaration: the automatic form is rejected because
// the name is collected, and the static form is accepted because it is not.
// The declaration and the use stand in the same block because a
// block_item_declaration is local to the block that holds it, so no conforming
// source declares the variable in one of these links and uses it outside.
TEST(DeferredAssertionElaboration,
     AutomaticDeclaredInAForkArmToRefFormalRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task caller;\n"
      "    fork\n"
      "      automatic int loc;\n"
      "      assert #0 (1) upd(loc);\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot pass automatic variable as actual for ref "
                            "formal 'r' in deferred-assertion call",
                            6, "16.4"));
}

TEST(DeferredAssertionElaboration,
     StaticDeclaredInAForkArmToRefFormalAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task caller;\n"
      "    fork\n"
      "      int loc;\n"
      "      assert #0 (1) upd(loc);\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DeferredAssertionElaboration,
     AutomaticDeclaredUnderARandcaseArmToRefFormalRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task caller;\n"
      "    randcase\n"
      "      1 : begin\n"
      "        automatic int loc;\n"
      "        assert #0 (1) upd(loc);\n"
      "      end\n"
      "    endcase\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot pass automatic variable as actual for ref "
                            "formal 'r' in deferred-assertion call",
                            7, "16.4"));
}

TEST(DeferredAssertionElaboration,
     StaticDeclaredUnderARandcaseArmToRefFormalAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task caller;\n"
      "    randcase\n"
      "      1 : begin\n"
      "        int loc;\n"
      "        assert #0 (1) upd(loc);\n"
      "      end\n"
      "    endcase\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DeferredAssertionElaboration,
     AutomaticDeclaredInARandsequenceCodeBlockToRefFormalRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task caller;\n"
      "    randsequence(main)\n"
      "      main : { automatic int loc; assert #0 (1) upd(loc); };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot pass automatic variable as actual for ref "
                            "formal 'r' in deferred-assertion call",
                            5, "16.4"));
}

TEST(DeferredAssertionElaboration,
     StaticDeclaredInARandsequenceCodeBlockToRefFormalAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task automatic upd(ref int r); endtask\n"
      "  task caller;\n"
      "    randsequence(main)\n"
      "      main : { int loc; assert #0 (1) upd(loc); };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
