#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

// §7.4.6 states the operations an associative array as a whole admits:
// "Associative arrays cannot be sliced, but reading, writing and equality
// operations can be performed on such arrays as a whole or on a single element
// of such an array". An arithmetic operator is none of the three, so it
// requires the array to be selected down to an element first, and the clause
// names no statement in which the requirement is suspended.
//
// The seven cases here are the seven statement positions
// ElaboratorOperationRules::WalkStmtsForAssocOperand in
// src/elaborator/elaborator_validate_operations_arrays.cpp reached only once it
// took its list of nested statements from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. Each of the seven elaborated
// clean beforehand, with the whole array left standing as an arithmetic
// operand.

namespace {

// Reading, writing and equality are the three operations §7.4.6 allows on an
// associative array as a whole, so an arithmetic operator requires the array to
// be selected down to an element first, and the clause names no statement the
// requirement is suspended in. The rule is therefore owed wherever an
// expression can be written, which is wherever a statement can be written.
//
// ElaboratorOperationRules::WalkStmtsForAssocOperand in
// src/elaborator/elaborator_validate_operations_arrays.cpp reached six of the
// thirteen statement links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states. The seven cases here
// each put `x = aa + 1` in one of the seven positions it did not read, where
// the operand was never looked at rather than looked at and allowed.
//
// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword [ :
// block_identifier ]`, so a fork arm is a statement position like any other.
TEST(AssocArrayOperandElaboration, AssocOperandInAForkArmNames7_4_6) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  initial begin\n"
      "    fork\n"
      "      x = aa + 1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array operand requires an element", 6,
                            "7.4.6"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case covers
// the pass arm and the one below it the fail arm.
TEST(AssocArrayOperandElaboration,
     AssocOperandInAnAssertionPassStatementNames7_4_6) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  logic ok;\n"
      "  initial assert (ok) x = aa + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array operand requires an element", 5,
                            "7.4.6"));
}

TEST(AssocArrayOperandElaboration,
     AssocOperandInAnAssertionFailStatementNames7_4_6) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  logic ok;\n"
      "  initial assert (ok) else x = aa + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array operand requires an element", 5,
                            "7.4.6"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. The rule
// is a static one, so it holds whether the weighted draw would select the item
// or not.
TEST(AssocArrayOperandElaboration, AssocOperandInARandcaseItemNames7_4_6) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  initial randcase 1: x = aa + 1; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array operand requires an element", 4,
                            "7.4.6"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions.
TEST(AssocArrayOperandElaboration,
     AssocOperandInARandsequenceCodeBlockNames7_4_6) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = aa + 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array operand requires an element", 6,
                            "7.4.6"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments |
// for_variable_declaration { , for_variable_declaration }` and
// `for_step_assignment ::= operator_assignment | inc_or_dec_expression |
// function_subroutine_call`. A.6.2 gives `variable_assignment ::=
// variable_lvalue = expression` and `operator_assignment ::= variable_lvalue
// assignment_operator expression`, whose assignment_operator includes `=`, so
// an assignment stands at each of the two positions: this case writes one at
// the initialization and the case below it writes one at the step.
TEST(AssocArrayOperandElaboration,
     AssocOperandInAForLoopInitializationNames7_4_6) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  int i;\n"
      "  initial for (x = aa + 1; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array operand requires an element", 5,
                            "7.4.6"));
}

TEST(AssocArrayOperandElaboration, AssocOperandInAForLoopStepNames7_4_6) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; x = aa + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array operand requires an element", 5,
                            "7.4.6"));
}

}  // namespace
