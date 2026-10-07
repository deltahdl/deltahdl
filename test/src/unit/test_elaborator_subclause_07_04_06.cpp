#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

// §7.4.6 states the operations an associative array as a whole admits: no
// slicing, but reading, writing and equality on the whole array or on one
// element of it. An arithmetic operator is none of the three, so it requires
// the array to be selected down to an element first, and the clause names no
// statement in which the requirement is suspended.
//
// The seven cases here are seven statement positions a walk has to take its
// list of nested statements from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h to reach, as
// WalkStmtForAggregateOperands in
// src/elaborator/elaborator_validate_operations_aggregate.cpp does. A walk
// that named its own list left each of the seven elaborating clean, with the
// whole array left standing as an arithmetic operand.

namespace {

// Reading, writing and equality are the three operations §7.4.6 allows on an
// associative array as a whole, so an arithmetic operator requires the array to
// be selected down to an element first, and the clause names no statement the
// requirement is suspended in. The rule is therefore owed wherever an
// expression can be written, which is wherever a statement can be written.
//
// A walk naming six of the thirteen statement links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states would miss the rest. The
// seven cases here each put `x = aa + 1` in one of those seven positions, where
// such a walk never looks at the operand rather than looking and allowing it.
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

// §7.4.6: a variable of an integral type is no more an array than a number is,
// whether the module declares it, through a typedef or not, a block declares
// it, or a for loop's initialization does, so comparing an unpacked array with
// one is reported.
TEST(UnpackedArrayOperandElaboration, IntegralVariablesAreNoArrays) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  int a[3];\n"
      "  int x;\n"
      "  byte_t v;\n"
      "  logic [3:0] w;\n"
      "  initial begin\n"
      "    int y;\n"
      "    if (a == x) x = 1;\n"
      "    if (v != a) x = 2;\n"
      "    if (a === w) x = 3;\n"
      "    if (a == y) x = 4;\n"
      "    for (int i = 0; i < 3; i++) if (a == i) x = 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kCompared =
      "an unpacked array is compared only with another unpacked array";
  for (int line = 9; line <= 13; ++line) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, line, "7.4.6"))
        << "line " << line;
  }
}

// §11.4.5 and §11.4.6 give every equality, case equality and wildcard equality
// operator a 1-bit result, so §7.4.6 reports an unpacked array compared with
// one, from either side.
TEST(UnpackedArrayOperandElaboration, AnEqualityResultIsNoArray) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[3];\n"
      "  int x;\n"
      "  initial begin\n"
      "    if (a == (x == 1)) x = 1;\n"
      "    if ((x !== 1) != a) x = 2;\n"
      "    if (a == (x ==? 1)) x = 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kCompared =
      "an unpacked array is compared only with another unpacked array";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 5, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 6, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 7, "7.4.6"));
}

// A name a block declares stands for the block's declaration inside it: a
// block's `int a` hides the module's array `a`, and a block's array `x` the
// module's `int x`, so neither comparison here sets an array against an
// integral value. A variable of a typedef naming an unpacked array is no
// integral value either.
TEST(UnpackedArrayOperandElaboration, BlockDeclarationsHideTheModules) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef int row_t[3];\n"
      "  int a[3];\n"
      "  int x;\n"
      "  initial begin\n"
      "    int a;\n"
      "    if (a == 4) x = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    int x[3];\n"
      "    row_t r;\n"
      "    if (a == x) x[0] = 1;\n"
      "    if (a == r) x[0] = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.4.6 holds for an unpacked array a block declares as for one the module
// declares: a fixed-size array and a queue compared with an integral value,
// and a fixed-size array under an integral operator, are each reported, while
// an element compared with a number is not.
TEST(UnpackedArrayOperandElaboration, BlockArraysAreNoIntegralOperands) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    int b[3];\n"
      "    int q[$];\n"
      "    if (b == 4) x = 1;\n"
      "    x = b + 1;\n"
      "    if (q != x) x = 2;\n"
      "    if (b[1] == 4) x = 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kCompared =
      "an unpacked array is compared only with another unpacked array";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 6, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an unpacked array is not an operand of this "
                            "operator",
                            7, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 8, "7.4.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kCompared, 9, "7.4.6"));
}

// An associative array is an unpacked array, which §7.4.6 lets take part in an
// equality as a whole only against another array: one the module declares and
// one a block declares are each reported compared with an integral value, and
// two compared with each other are not.
TEST(UnpackedArrayOperandElaboration, AssociativeArraysAreNoIntegralOperands) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int aa[string];\n"
      "  int x;\n"
      "  initial begin\n"
      "    int ab[int];\n"
      "    if (aa == 4) x = 1;\n"
      "    if (x != ab) x = 2;\n"
      "    if (aa == ab) x = 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kCompared =
      "an unpacked array is compared only with another unpacked array";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 6, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 7, "7.4.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kCompared, 8, "7.4.6"));
}

// §7.4.6 keeps an associative array a block declares from being treated as an
// integer, as it does one the module declares, and a block's `int aa` hides
// the module's associative array `aa`, so adding to it is an integer's sum.
TEST(AssocArrayOperandElaboration, BlockDeclarationsAreSeenInScope) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int x;\n"
      "  initial begin\n"
      "    int ab[string];\n"
      "    x = ab + 1;\n"
      "  end\n"
      "  initial begin\n"
      "    int aa;\n"
      "    x = aa + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array operand requires an element", 6,
                            "7.4.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "associative array operand requires an element",
                             10, "7.4.6"));
}

// §6.7.1 gives a net declared with a net type alone the implicit logic data
// type, so §7.4.6 reports an unpacked array compared with one as with any
// integral value.
TEST(UnpackedArrayOperandElaboration, NetsAreNoArrays) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[3];\n"
      "  wire [3:0] w;\n"
      "  wire logic v;\n"
      "  int x;\n"
      "  initial begin\n"
      "    if (a == w) x = 1;\n"
      "    if (v != a) x = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kCompared =
      "an unpacked array is compared only with another unpacked array";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 7, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 8, "7.4.6"));
}

}  // namespace
