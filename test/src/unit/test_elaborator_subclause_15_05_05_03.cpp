#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §15.5.5.3: the equality, inequality, case-equality, and case-inequality
// operators are the only comparison operators permitted on event variables,
// and an event may be used as a Boolean test. These uses elaborate cleanly.
TEST(EventComparisonElaborator, AllowedComparisonOperatorsAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event a, b;\n"
             "  logic w, x, y, z, t;\n"
             "  initial begin\n"
             "    w = (a == b);\n"
             "    x = (a != b);\n"
             "    y = (a === b);\n"
             "    z = (a !== b);\n"
             "    if (a) t = 1;\n"
             "  end\n"
             "endmodule\n"));
}

// §15.5.5.3: an event may be compared against the special value null with any
// of the permitted equality operators, including the case-equality forms.
TEST(EventComparisonElaborator, ComparisonAgainstNullAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event a;\n"
             "  logic w, x, y, z;\n"
             "  initial begin\n"
             "    w = (a == null);\n"
             "    x = (a != null);\n"
             "    y = (a === null);\n"
             "    z = (a !== null);\n"
             "  end\n"
             "endmodule\n"));
}

// §15.5.5.3: a relational operator is not among the permitted operators for an
// event variable, so applying one is illegal.
TEST(EventComparisonElaborator, RelationalOperatorRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic x;\n"
      "  initial x = (a < b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '<' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

// §15.5.5.3: an arithmetic operator on an event operand is likewise illegal,
// even when the other operand is not an event.
TEST(EventComparisonElaborator, ArithmeticOperatorRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a;\n"
      "  logic [31:0] x;\n"
      "  initial x = a + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '+' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

// §15.5.5.3: a bitwise operator on an event operand is not a permitted
// comparison and is rejected.
TEST(EventComparisonElaborator, BitwiseOperatorRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic x;\n"
      "  initial x = (a & b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '&' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

// §15.5.5.3: a unary operator applied to an event operand is outside the set of
// permitted operations and is rejected.
TEST(EventComparisonElaborator, UnaryOperatorRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a;\n"
      "  logic [31:0] x;\n"
      "  initial x = ~a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unary operator '~' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

// §15.5.5.3: a postfix increment/decrement on an event operand is likewise not
// among the permitted operations and is rejected.
TEST(EventComparisonElaborator, PostfixIncrementOperatorRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a;\n"
      "  logic [31:0] x;\n"
      "  initial x = a++;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "postfix operator '++' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

// §15.5.5.3: a unary arithmetic operator reaches the same check as the unary
// bitwise negation above, so the report has to name which of them was written.
// Table 11-1 lists '-' and '~' as different operators under different names.
TEST(EventComparisonElaborator, UnaryOperatorReportNamesTheOperator) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a;\n"
      "  logic [31:0] x;\n"
      "  initial x = -a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unary operator '-' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

// The property the three checks exist to be told apart by. All three stand at
// the same line under the same subclause, so while they shared one sentence a
// test written for any one of them was satisfied by the other two, and deleting
// a check reported failures against tests covering the checks that remained.
// One source draws all three at once, and the assertions are what say the
// reports differ.
TEST(EventComparisonElaborator, OperatorKindsReportDistinguishably) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic [31:0] x, y, z;\n"
      "  initial x = a + b;\n"
      "  initial y = ~a;\n"
      "  initial z = a++;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '+' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unary operator '~' is not allowed on event "
                            "variable",
                            5, "15.5.5.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "postfix operator '++' is not allowed on event "
                            "variable",
                            6, "15.5.5.3"));
}

// §15.5.5.3 admits only ==, !=, === and !== on an event variable and names no
// statement the rule is suspended in. Elaborator::WalkStmtsForEventOps in
// src/elaborator/elaborator_validate_datatype_ops.cpp had written out six of
// the thirteen child-statement links Stmt declares, so the addition of
// ArithmeticOperatorRejected above elaborated clean in any of the other seven.
// The walk now takes its list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h, and each case below rewrites
// that addition in one newly reached position.
//
// Parser::IsDataTypeKeyword in src/parser/parser_stmt.cpp omits
// TokenKind::kKwEvent, so an event variable cannot be declared inside a
// begin/end block, a fork arm or a subroutine body (issue #3322). Every case
// below therefore declares the event as a module item and writes only the
// offending operation in the new position, which is what the rule is about.

// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword`, whose
// statements the parser keeps in Stmt::fork_stmts.
TEST(EventComparisonElaborator, ArithmeticOperatorInForkArmRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic [31:0] x;\n"
      "  initial fork\n"
      "    x = a + b;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '+' is not allowed on event "
                            "variable",
                            5, "15.5.5.3"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...` and
// `variable_assignment ::= variable_lvalue = expression`, so an assignment
// whose right-hand side adds two events stands in a for-loop header. The parser
// keeps it in Stmt::for_inits.
TEST(EventComparisonElaborator, ArithmeticOperatorInForInitializationRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic [31:0] x;\n"
      "  initial for (x = a + b; x < 1; x = x + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '+' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, and an operator_assignment
// written with `=` carries an arbitrary expression. The parser keeps it in
// Stmt::for_steps.
TEST(EventComparisonElaborator, ArithmeticOperatorInForStepRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic [31:0] x;\n"
      "  initial for (x = 0; x < 1; x = a + b) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '+' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

// A.6.10 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion (§16.3) holds a statement in
// each arm, kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This
// case and the next cover one arm each.
TEST(EventComparisonElaborator,
     ArithmeticOperatorInAssertionPassStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic [31:0] x;\n"
      "  initial assert (1) x = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '+' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

TEST(EventComparisonElaborator,
     ArithmeticOperatorInAssertionFailStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic [31:0] x;\n"
      "  initial assert (1) else x = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '+' is not allowed on event "
                            "variable",
                            4, "15.5.5.3"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second of each Stmt::randcase_items pair.
TEST(EventComparisonElaborator, ArithmeticOperatorInRandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic [31:0] x;\n"
      "  initial randcase\n"
      "    1 : x = a + b;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '+' is not allowed on event "
                            "variable",
                            5, "15.5.5.3"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block (§18.17) holds ordinary
// procedural statements. The parser keeps them in RsProd::code_stmts, reached
// through Stmt::rs_productions and through no other member of Stmt.
TEST(EventComparisonElaborator,
     ArithmeticOperatorInRandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = a + b; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '+' is not allowed on event "
                            "variable",
                            6, "15.5.5.3"));
}

}  // namespace
