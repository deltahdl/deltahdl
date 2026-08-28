#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §13.3.1: items of an automatic task cannot be reached through a hierarchical
// reference. A hierarchical path into an automatic task's local is rejected.
TEST(StaticAutomaticTask, AutoTaskItemHierRefInContAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "  endtask\n"
      "  assign y = t.x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic task is not permitted", 6,
      "13.3.1"));
}

// Contrast: the same hierarchical path into a static task is permitted, so the
// §13.3.1 restriction must not fire for a static task.
TEST(StaticAutomaticTask, StaticTaskItemHierRefAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  task static t();\n"
      "    int x;\n"
      "  endtask\n"
      "  assign y = t.x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The restriction also applies to references inside procedural blocks.
TEST(StaticAutomaticTask, AutoTaskItemHierRefInInitialError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "  endtask\n"
      "  initial y = t.x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic task is not permitted", 6,
      "13.3.1"));
}

// §13.3.1 says the items of an automatic task "are allocated dynamically for
// each concurrent task entry" and "cannot be accessed by hierarchical
// references", naming no position such a reference is allowed to stand in, so
// every position a statement holds a statement in is one the report reaches.
// WalkStmtsForAutoRef in
// src/elaborator/elaborator_validate_hier_refs.cpp had written out nine of
// the thirteen child-statement links Stmt declares and now takes the
// list from ForEachChildStmt in src/elaborator/elaborator_validate_internal.h.
// The four cases below stand in the four positions it was missing. The same
// walk carries §13.4.2's report for a function, whose four cases are in
// test/src/unit/test_elaborator_subclause_13_04_02.cpp.

// A.6.10 gives `simple_immediate_assert_statement ::= assert ( expression )
// action_block` and §16.3 gives `action_block ::= statement_or_null |
// [ statement ] else statement_or_null`, so the pass arm of an immediate
// assertion holds an ordinary statement, kept in Stmt::assert_pass_stmt.
TEST(StaticAutomaticTask, AutoTaskItemHierRefInAnAssertionPassStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  logic ok;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "  endtask\n"
      "  initial assert (ok) y = t.x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic task is not permitted", 7,
      "13.3.1"));
}

// The else arm of the same production, kept in Stmt::assert_fail_stmt, a link
// the pass-arm case above does not reach.
TEST(StaticAutomaticTask, AutoTaskItemHierRefInAnAssertionFailStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic held;\n"
      "  logic armed;\n"
      "  task automatic drain();\n"
      "    int depth;\n"
      "  endtask\n"
      "  initial assert (armed) else held = drain.depth;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic task is not permitted", 7,
      "13.3.1"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. §13.3.1
// bars the reference rather than the execution, so the report stands whether
// the weighted draw would select the item or not.
TEST(StaticAutomaticTask, AutoTaskItemHierRefInARandcaseItemError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic taken;\n"
      "  task automatic pick();\n"
      "    int chosen;\n"
      "  endtask\n"
      "  initial randcase 1: taken = pick.chosen; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic task is not permitted", 6,
      "13.3.1"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(StaticAutomaticTask, AutoTaskItemHierRefInARandsequenceCodeBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic kept;\n"
      "  task automatic sample();\n"
      "    int sampled;\n"
      "  endtask\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { kept = sample.sampled; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic task is not permitted", 8,
      "13.3.1"));
}

}  // namespace
