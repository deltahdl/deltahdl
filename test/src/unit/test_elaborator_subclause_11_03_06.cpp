#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AssignmentWithinExpressionElaboration, SimpleAssignInExprInProcedural) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic a, b;\n"
             "  initial if ((a = b)) ;\n"
             "endmodule\n"));
}

TEST(AssignmentWithinExpressionElaboration, CompoundAssignInExprInProcedural) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int a;\n"
             "  initial a = (a += 1);\n"
             "endmodule\n"));
}

TEST(AssignmentWithinExpressionElaboration, AssignInContinuousAssignIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  logic a, b, c;\n"
      "  assign c = (a = b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is illegal",
                            3, "11.3.6"));
}

// §11.3.6: an assignment operator is illegal in an expression within a
// procedural continuous assignment.
TEST(AssignmentWithinExpressionElaboration,
     AssignInProceduralContinuousAssignIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  logic a, b, c;\n"
      "  initial assign c = (a = b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is illegal",
                            3, "11.3.6"));
}

// The same procedural continuous assignment without an embedded assignment
// operator is legal, confirming it is the assignment-in-expression that is
// rejected above.
TEST(AssignmentWithinExpressionElaboration,
     ProceduralContinuousAssignWithoutEmbeddedAssignIsLegal) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic a, c;\n"
             "  initial assign c = a;\n"
             "endmodule\n"));
}

// §11.3.6 says "It shall be illegal to include an assignment operator in an
// event expression, in an expression within a procedural continuous
// assignment, or in an expression that is not within a procedural statement",
// and names no statement the procedural continuous assignment may stand in to
// escape that.
// ElaboratorOperationRules::WalkStmtsForAssignInExpr in
// src/elaborator/elaborator_validate_cast_ops.cpp had written out six of the
// thirteen child-statement links Stmt declares and now takes the list from
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h. The five
// cases below are
// AssignmentWithinExpressionElaboration.AssignInProceduralContinuousAssignIsIllegal
// above rewritten in five of the seven positions the walk was missing, each of
// which elaborated clean beforehand with the embedded assignment unreported.
//
// Stmt::for_inits and Stmt::for_steps get no case. A.6.8 gives
// `for_initialization ::= list_of_variable_assignments |
// for_variable_declaration { , for_variable_declaration }` and
// `for_step_assignment ::= operator_assignment | inc_or_dec_expression |
// function_subroutine_call`, and A.6.2 gives `procedural_continuous_assignment
// ::= assign variable_assignment | ...`, which is a statement_item and none of
// those five forms. No `assign` statement can be written at either end of a
// loop header, so both links are descended for the list's sake rather than for
// an instance.

// A.6.3 gives `par_block ::= fork [ : block_identifier ]
// { block_item_declaration } { statement_or_null } join_keyword ...`, so a fork
// holds statements the way a begin-end block does. The parser keeps them in
// Stmt::fork_stmts rather than in Stmt::stmts.
TEST(AssignmentWithinExpressionElaboration,
     AssignInProceduralContinuousAssignInForkArmIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic a, b, c;\n"
      "  initial fork\n"
      "    assign c = (a = b);\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is illegal",
                            4, "11.3.6"));
}

// A.6.10 gives `simple_immediate_assert_statement ::= assert ( expression )
// action_block` and §16.3 gives `action_block ::= statement_or_null |
// [ statement ] else statement_or_null`, so the pass arm of an immediate
// assertion holds an ordinary statement, kept in Stmt::assert_pass_stmt.
TEST(AssignmentWithinExpressionElaboration,
     AssignInProceduralContinuousAssignInAssertionPassStatementIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic a, b, c;\n"
      "  logic ok;\n"
      "  initial assert (ok) assign c = (a = b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is illegal",
                            4, "11.3.6"));
}

// The else arm of the same production, kept in Stmt::assert_fail_stmt, a link
// the pass-arm case above does not reach.
TEST(AssignmentWithinExpressionElaboration,
     AssignInProceduralContinuousAssignInAssertionFailStatementIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic a, b, c;\n"
      "  logic armed;\n"
      "  initial assert (armed) else assign c = (a = b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is illegal",
                            4, "11.3.6"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. §11.3.6
// judges the expression as written rather than what runs, so the report stands
// whether the weighted draw would select the item or not.
TEST(AssignmentWithinExpressionElaboration,
     AssignInProceduralContinuousAssignInRandcaseItemIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic a, b, c;\n"
      "  initial randcase 1: assign c = (a = b); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is illegal",
                            3, "11.3.6"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(AssignmentWithinExpressionElaboration,
     AssignInProceduralContinuousAssignInRandsequenceCodeBlockIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic a, b, c;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { assign c = (a = b); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment operator within expression is illegal",
                            5, "11.3.6"));
}

}  // namespace
