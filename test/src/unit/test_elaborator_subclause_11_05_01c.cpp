#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

// §11.5.1 says of a non-indexed part-select `vect[msb_expr:lsb_expr]` that
// "The first expression shall address a more significant bit than the second
// expression", and states no condition on where the select stands. §11.5 makes
// a part-select an operand, so the rule is owed wherever an expression can be
// written, which is wherever a statement can be written. The four cases here
// each put one reversed part-select in one statement position.
//
// Each of those four is a position Elaborator::ValidatePartSelectBounds reached
// only once CheckPartSelectBoundsStmt in
// src/elaborator/elaborator_validate_queries_dims.cpp took its list of nested
// statements from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. Every one of them elaborated
// clean beforehand, with a reversed part-select left unreported.
//
// Every vector below is declared [7:4] rather than [7:0] so that an index and
// the storage offset it reaches are different numbers. On [7:0] the two
// coincide, and a check that computed an offset where §11.5.1 requires an index
// would answer such a case the same way the rule does, which
// docs/tenets/tests/UNIT_TESTS.md bars.

namespace {

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case covers
// the pass arm and the one below it the fail arm.
TEST(SelectElaboration,
     ReversedPartSelectInAnAssertionPassStatementNames11_5_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:4] v;\n"
      "  logic [3:0] result;\n"
      "  logic ok;\n"
      "  initial assert (ok) result = v[4:7];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more", 5,
                            "11.5.1"));
}

TEST(SelectElaboration,
     ReversedPartSelectInAnAssertionFailStatementNames11_5_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:4] word;\n"
      "  logic [3:0] out;\n"
      "  logic passed;\n"
      "  initial assert (passed) else out = word[4:7];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more", 5,
                            "11.5.1"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. §11.5.1's
// ordering rule is a static one, so it holds whether the weighted draw would
// select the item or not.
TEST(SelectElaboration, ReversedPartSelectInARandcaseItemNames11_5_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:4] bus;\n"
      "  logic [3:0] taken;\n"
      "  initial randcase 1: taken = bus[4:7]; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more", 4,
                            "11.5.1"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions.
TEST(SelectElaboration, ReversedPartSelectInARandsequenceCodeBlockNames11_5_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:4] src;\n"
      "  logic [3:0] dst;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { dst = src[4:7]; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more", 6,
                            "11.5.1"));
}

// §11.4.12 says of a select of a concatenation that "Such a select shall not be
// legal as a net_lvalue, variable_lvalue, or in any equivalent use, such as on
// the left-hand side of an assignment", and states no condition on the
// statement the assignment stands in. The report names §11.4.12 rather than
// this file's §11.5.1, because it is the concatenation and not the bounds of
// the select that makes the lvalue illegal.
//
// ElaboratorOperationRules::WalkStmtsForSelectOnConcatLvalue in
// src/elaborator/elaborator_validate_operations_arrays.cpp reached six of the
// thirteen statement links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states. The seven cases here
// each put `{a, b}[2] = 1'b1` in one of the seven positions it did not read,
// every one of which elaborated clean beforehand.
//
// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword [ :
// block_identifier ]`, so a fork arm is a statement position like any other.
TEST(SelectElaboration, SelectOnConcatLvalueInAForkArmNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      {a, b}[2] = 1'b1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "select of a concatenation shall not be used", 5,
                            "11.4.12"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case covers
// the pass arm and the one below it the fail arm.
TEST(SelectElaboration,
     SelectOnConcatLvalueInAnAssertionPassStatementNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  logic ok;\n"
      "  initial assert (ok) {a, b}[2] = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "select of a concatenation shall not be used", 4,
                            "11.4.12"));
}

TEST(SelectElaboration,
     SelectOnConcatLvalueInAnAssertionFailStatementNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  logic ok;\n"
      "  initial assert (ok) else {a, b}[2] = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "select of a concatenation shall not be used", 4,
                            "11.4.12"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. The rule
// is a static one, so it holds whether the weighted draw would select the item
// or not.
TEST(SelectElaboration, SelectOnConcatLvalueInARandcaseItemNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  initial randcase 1: {a, b}[2] = 1'b1; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "select of a concatenation shall not be used", 3,
                            "11.4.12"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions.
TEST(SelectElaboration,
     SelectOnConcatLvalueInARandsequenceCodeBlockNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { {a, b}[2] = 1'b1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "select of a concatenation shall not be used", 5,
                            "11.4.12"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments |
// for_variable_declaration { , for_variable_declaration }` and
// `for_step_assignment ::= operator_assignment | inc_or_dec_expression |
// function_subroutine_call`. A.6.2 gives `variable_assignment ::=
// variable_lvalue = expression` and `operator_assignment ::= variable_lvalue
// assignment_operator expression`, whose assignment_operator includes `=`, so
// an assignment stands at each of the two positions: this case writes one at
// the initialization and the case below it writes one at the step.
TEST(SelectElaboration,
     SelectOnConcatLvalueInAForLoopInitializationNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  int i;\n"
      "  initial for ({a, b}[2] = 1'b1; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "select of a concatenation shall not be used", 4,
                            "11.4.12"));
}

TEST(SelectElaboration, SelectOnConcatLvalueInAForLoopStepNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; {a, b}[2] = 1'b1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "select of a concatenation shall not be used", 4,
                            "11.4.12"));
}

}  // namespace
