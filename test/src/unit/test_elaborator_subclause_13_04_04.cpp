#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(FunctionBackgroundProcessElaboration, ForkJoinNoneOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void my_func();\n"
      "    fork\n"
      "      a = 1;\n"
      "    join_none\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, NonblockingAssignOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  function void set_x();\n"
      "    x <= 1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, EventTriggerOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  function void fire_event();\n"
      "    -> e;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.4.4: a clocking drive is one of the non-blocking statements that shall
// be allowed inside a function (alongside nonblocking assignments, event
// triggers, and fork-join_none). The synchronous drive syntax comes from the
// §14.16 dependency: a nonblocking assignment to a clocking-block output.
TEST(FunctionBackgroundProcessElaboration, ClockingDriveOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic sig;\n"
      "  clocking cb @(posedge clk);\n"
      "    output sig;\n"
      "  endclocking\n"
      "  function void drive_it();\n"
      "    cb.sig <= 1'b1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, DelayInsideForkJoinNoneOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void spawn_delayed();\n"
      "    fork\n"
      "      #10 $display(\"done\");\n"
      "    join_none\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, ForkJoinError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void my_func();\n"
      "    fork\n"
      "      a = 1;\n"
      "    join\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  // The rejection is §13.4's rule on which join form a function may contain,
  // not the §13.4.4 rule this file is named for.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only fork/join_none is permitted inside a function", 3, "13.4"));
}

TEST(FunctionBackgroundProcessElaboration, ForkJoinAnyError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void my_func();\n"
      "    fork\n"
      "      a = 1;\n"
      "    join_any\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  // As above, §13.4 is the rule that rejects a join_any inside a function.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only fork/join_none is permitted inside a function", 3, "13.4"));
}

TEST(FunctionBackgroundProcessElaboration, TaskEnableInsideForkJoinNoneOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t(); endtask\n"
      "  function void f();\n"
      "    fork\n"
      "      t();\n"
      "    join_none\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, ContAssignToFuncWithNbaError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  logic r;\n"
      "  function automatic logic spawn_nba();\n"
      "    q <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  assign r = spawn_nba();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "function 'spawn_nba' schedules a background event and cannot be called "
      "outside an initial/always procedure or fork block",
      8, "13.4.4"));
}

TEST(FunctionBackgroundProcessElaboration,
     ContAssignToFuncWithForkJoinNoneError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic r;\n"
      "  function automatic logic spawn_bg();\n"
      "    fork\n"
      "      $display(\"bg\");\n"
      "    join_none\n"
      "    return 1'b1;\n"
      "  endfunction\n"
      "  assign r = spawn_bg();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "function 'spawn_bg' schedules a background event and cannot be called "
      "outside an initial/always procedure or fork block",
      9, "13.4.4"));
}

TEST(FunctionBackgroundProcessElaboration,
     ContAssignToFuncWithEventTriggerError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  logic r;\n"
      "  function automatic logic spawn_trigger();\n"
      "    -> e;\n"
      "    return 1'b1;\n"
      "  endfunction\n"
      "  assign r = spawn_trigger();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'spawn_trigger' schedules a background "
                            "event and cannot be called outside an "
                            "initial/always procedure or fork block",
                            8, "13.4.4"));
}

TEST(FunctionBackgroundProcessElaboration, NbEventTriggerOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  function void fire_nb();\n"
      "    ->> e;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration,
     ContAssignToFuncWithNbEventTriggerError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  logic r;\n"
      "  function automatic logic spawn_nb_trigger();\n"
      "    ->> e;\n"
      "    return 1'b1;\n"
      "  endfunction\n"
      "  assign r = spawn_nb_trigger();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'spawn_nb_trigger' schedules a background "
                    "event and cannot be called outside an "
                    "initial/always procedure or fork block",
                    8, "13.4.4"));
}

TEST(FunctionBackgroundProcessElaboration, ContAssignToPureFuncOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic r;\n"
      "  function automatic logic pure_func(input logic a);\n"
      "    return ~a;\n"
      "  endfunction\n"
      "  logic in;\n"
      "  assign r = pure_func(in);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.4.4: the LRM's own illegal example is a variable-declaration
// initializer (`bit y = watch_for_zero(stack);`). A module-scope variable
// initializer runs at time zero, outside any initial/always/fork procedure,
// so calling a function that schedules a background event there is illegal.
TEST(FunctionBackgroundProcessElaboration, VarInitToBackgroundFuncNbaError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  function automatic logic spawn_nba();\n"
      "    q <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  logic y = spawn_nba();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "function 'spawn_nba' schedules a background event and cannot be called "
      "outside an initial/always procedure or fork block",
      7, "13.4.4"));
}

// §13.4.4: a net-declaration assignment is a continuous assignment, another
// context in which the side effect of spawning a background event is not
// allowed.
TEST(FunctionBackgroundProcessElaboration, NetDeclInitToBackgroundFuncError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  function automatic logic spawn_nba();\n"
      "    q <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  wire y = spawn_nba();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "function 'spawn_nba' schedules a background event and cannot be called "
      "outside an initial/always procedure or fork block",
      7, "13.4.4"));
}

// §13.4.4: a variable initializer that calls an ordinary function with no
// background side effect stays legal — the rule flags only the side effect.
TEST(FunctionBackgroundProcessElaboration, VarInitToPureFuncOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic logic pure_func(input logic a);\n"
      "    return ~a;\n"
      "  endfunction\n"
      "  logic in;\n"
      "  logic y = pure_func(in);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, InitialCallToBackgroundFuncOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  function automatic logic spawn_nba();\n"
      "    q <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  logic r;\n"
      "  initial r = spawn_nba();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.4.4 asks whether the called function schedules an event that cannot
// become active until after it returns, and puts no condition on where the
// statement that schedules it stands. StmtSpawnsBackgroundProcess in
// src/elaborator/elaborator_validate_subroutine.cpp had written out ten of the
// thirteen child-statement links Stmt declares, and now takes the list from
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h. The two
// cases below cover the one newly reached position a background-spawning
// statement can be written in. Stmt::for_inits and Stmt::for_steps are the
// other two and get no case: A.6.8 admits only a variable assignment or a
// for_variable_declaration in a for_initialization, and only an
// operator_assignment, an inc_or_dec_expression or a function_subroutine_call
// in a for_step, so a nonblocking assignment, an event trigger and a fork are
// all barred from both.

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements and a nonblocking assignment written there schedules the event
// §13.4.4 is about. The statements are kept in RsProd::code_stmts, reached
// through Stmt::rs_productions and through no other member of Stmt.
TEST(FunctionBackgroundProcessElaboration,
     ContAssignToFuncWithNbaInRandsequenceCodeBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  logic r;\n"
      "  function automatic logic spawn_rs();\n"
      "    randsequence(main)\n"
      "      main : { q <= 1'b1; };\n"
      "    endsequence\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  assign r = spawn_rs();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "function 'spawn_rs' schedules a background event and cannot be called "
      "outside an initial/always procedure or fork block",
      10, "13.4.4"));
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second list under
// Stmt::rs_productions, so a walk reaches it without reaching
// RsProd::code_stmts and the case above does not answer for it.
TEST(FunctionBackgroundProcessElaboration,
     ContAssignToFuncWithNbaInRandsequenceWeightCodeBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  logic r;\n"
      "  int i;\n"
      "  function automatic logic spawn_rs_weight();\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { q <= 1'b1; };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  assign r = spawn_rs_weight();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'spawn_rs_weight' schedules a background "
                            "event and cannot be called outside an "
                            "initial/always procedure or fork block",
                            12, "13.4.4"));
}

}  // namespace
