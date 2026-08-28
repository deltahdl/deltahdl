#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(TaskElaboration, TaskDeclInModuleElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task my_task(input int a);\n"
      "    $display(\"a=%0d\", a);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TaskElaboration, TaskWithOutputArgsElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task compute(input int a, output int b);\n"
      "    b = a * 2;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, TaskWithInoutArgElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task inc(inout int v);\n"
      "    v = v + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, TaskEmptyBodyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task nop;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, TaskEnablesTaskElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task inner;\n"
      "  endtask\n"
      "  task outer;\n"
      "    inner();\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, TaskWithRefArgElaborates) {
  ElabFixture f;
  // §13.5.2: pass-by-reference is illegal in a static-lifetime subroutine, so a
  // ref argument requires an automatic (or ref static) subroutine.
  auto* design = Elaborate(
      "module m;\n"
      "  task automatic inc(ref int v);\n"
      "    v = v + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, RefStaticQualifierStickyInheritedAtElaboration) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task t(ref static int a, b);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->function_decls.size(), 1u);
  auto* tk = mod->function_decls[0];
  ASSERT_EQ(tk->func_args.size(), 2u);
  EXPECT_EQ(tk->func_args[0].direction, Direction::kRef);
  EXPECT_TRUE(tk->func_args[0].is_ref_static);
  EXPECT_EQ(tk->func_args[1].direction, Direction::kRef);
  EXPECT_TRUE(tk->func_args[1].is_ref_static);
}

// §13.3: a task exits at endtask or at a return statement, and that return
// carries no value. The report that rejects one that does names the subclause
// stating the rule, so a caller learns which rule was enforced without matching
// the wording of the message.
TEST(TaskElaboration, ReturnValueDeclaredNames13_3) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    return 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "task returns a value", 3, "13.3"));
}

// The four cases below cover the positions CheckTaskBodyStmt in
// src/elaborator/elaborator_validate_funcbody.cpp reaches for the first time
// now that it takes its child-statement links from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. It had written out seven of
// the thirteen links Stmt declares, so §13.3's report on a return carrying a
// value went unmade for one written in Stmt::assert_pass_stmt,
// Stmt::assert_fail_stmt, Stmt::randcase_items or Stmt::rs_productions.
//
// Stmt::for_inits and Stmt::for_steps are newly reached too and get no case
// here: A.6.8 admits no jump_statement in either. The §13.3.2 rules the same
// walk carries do reach a for step, and
// TaskBodyElaboration.AutoTaskLocalInMonitorInAForStepError in
// test/src/unit/test_elaborator_subclause_13_03_02.cpp covers that.

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each.
TEST(TaskElaboration, ReturnValueInAnAssertionPassStmtIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    assert (1) return 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "task returns a value", 3, "13.3"));
}

TEST(TaskElaboration, ReturnValueInAnAssertionFailStmtIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    assert (1) else return 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "task returns a value", 3, "13.3"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry.
TEST(TaskElaboration, ReturnValueInARandcaseItemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    randcase 1 : return 1; endcase\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "task returns a value", 3, "13.3"));
}

// The §18.17.6 case: what a return written in a randsequence production code
// block is, and what §13.3 therefore owes it. "The return statement aborts the
// generation of the current production", and §18.17.7 adds that "A value is
// returned from a production by using the return with an expression", so a
// production declared `int` returns its value exactly the way §13.3's "task
// returns a value" report fires -- a return carrying an expression. Neither
// return below is the task's, so neither is that report's. Take
// TaskBodyScope::in_production_code_block in
// src/elaborator/elaborator_validate_funcbody.cpp away and §18.17.7's own
// construct is rejected inside a task.
TEST(TaskElaboration, ValueReturningProductionInATaskOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    randsequence(main)\n"
      "      void main : a { return; };\n"
      "      int a : { return 7; };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
