#include <gtest/gtest.h>

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

// §7.4.6 allows equality on an unpacked array only against another array and
// keeps an unpacked array from being treated as an integer: comparing a whole
// array or a row of a two-dimensional one with a number, and adding to one, are
// each reported on the array operand's line.
TEST(UnpackedArrayOperandElaboration, AnUnpackedArrayIsNoIntegralOperand) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[3];\n"
      "  int m[2][3];\n"
      "  int x;\n"
      "  initial begin\n"
      "    if (a == 4) x = 1;\n"
      "    if (m[1] != 4) x = 2;\n"
      "    x = a + 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kCompared =
      "an unpacked array is compared only with another unpacked array";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 6, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 7, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an unpacked array is not an operand of this "
                            "operator",
                            8, "7.4.6"));
}

// §7.4.6: an unpacked array compared with any plainly integral or real value is
// reported -- an unbased unsized literal, a real literal, the result of a
// binary arithmetic operator and that of a unary one -- and a unary operator
// that takes integral operands is no more applied to an array than a binary
// one.
TEST(UnpackedArrayOperandElaboration, EveryIntegralOperandKindIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[3];\n"
      "  int x;\n"
      "  initial begin\n"
      "    if (a == '1) x = 1;\n"
      "    if (a != 1.5) x = 2;\n"
      "    if (a == x + 1) x = 3;\n"
      "    if (-x != a) x = 4;\n"
      "    x = -a;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kCompared =
      "an unpacked array is compared only with another unpacked array";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 5, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 6, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 7, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 8, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an unpacked array is not an operand of this "
                            "operator",
                            9, "7.4.6"));
}

// §7.4.6: equality between two unpacked arrays, between slices of them and
// between rows of a two-dimensional one, and between an element and a number,
// are all allowed and elaborate clean.
TEST(UnpackedArrayOperandElaboration, ArraysComparedWithArraysAreAllowed) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[3], b[3];\n"
      "  int m[2][3];\n"
      "  int x;\n"
      "  initial begin\n"
      "    if (a == b) x = 1;\n"
      "    if (a[0:1] != b[1:2]) x = 2;\n"
      "    if (m[1] == m[0]) x = 3;\n"
      "    if (a[2] == 4) x = x + a[1];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
