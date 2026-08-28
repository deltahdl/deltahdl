#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ArrayOrderingElaboration, ArrayReverseOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:2];\n"
             "  initial arr.reverse();\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, ArraySortOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  initial arr.sort;\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, ArrayRsortOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  initial arr.rsort;\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, ArrayShuffleOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  initial arr.shuffle();\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, SortWithClauseOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  initial arr.sort with (item);\n"
             "endmodule\n"));
}

TEST(ArrayOrderingElaboration, RsortWithClauseOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [0:3];\n"
             "  initial arr.rsort with (item);\n"
             "endmodule\n"));
}

// §7.12.2: ordering methods apply to a dynamically sized array, not just a
// fixed one. The validator must recognize a dynamic array as a legal (non-
// associative) receiver and accept it, unlike the associative case below.
TEST(ArrayOrderingElaboration, SortOnDynamicArrayOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int a [] = '{3, 1, 2};\n"
             "  initial a.sort();\n"
             "endmodule\n"));
}

// §7.12.2: a queue is the other dynamically sized array form; it too is a legal
// ordering-method receiver and must elaborate without error.
TEST(ArrayOrderingElaboration, SortOnQueueOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q [$] = '{3, 1, 2};\n"
             "  initial q.sort;\n"
             "endmodule\n"));
}

// §7.12.2: specifying a with clause on reverse() is a compiler error.
TEST(ArrayOrderingElaboration, ReverseWithClauseIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [0:3];\n"
      "  initial arr.reverse() with (item);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'reverse' does not accept a "
                            "'with' clause",
                            3, "7.12.2"));
}

// §7.12.2: specifying a with clause on shuffle() is a compiler error.
TEST(ArrayOrderingElaboration, ShuffleWithClauseIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [0:3];\n"
      "  initial arr.shuffle() with (item);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'shuffle' does not accept a "
                            "'with' clause",
                            3, "7.12.2"));
}

// §7.12.2: ordering methods reorder fixed or dynamically sized unpacked
// arrays; an associative array is not a legal receiver.
TEST(ArrayOrderingElaboration, SortOnAssocArrayIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial arr.sort();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'sort' cannot be applied to "
                            "associative array 'arr'",
                            3, "7.12.2"));
}

TEST(ArrayOrderingElaboration, RsortOnAssocArrayIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial arr.rsort();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'rsort' cannot be applied "
                            "to associative array 'arr'",
                            3, "7.12.2"));
}

TEST(ArrayOrderingElaboration, ReverseOnAssocArrayIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial arr.reverse();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'reverse' cannot be applied "
                            "to associative array 'arr'",
                            3, "7.12.2"));
}

TEST(ArrayOrderingElaboration, ShuffleOnAssocArrayIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [int];\n"
      "  initial arr.shuffle();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'shuffle' cannot be applied "
                            "to associative array 'arr'",
                            3, "7.12.2"));
}

// §7.12.2 gives the array ordering methods no associative receiver, and states
// that of the receiver rather than of the statement the call is written in.
// WalkStmtsForArrayOrdering wrote out six of the thirteen statement links
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h states, so
// each source below elaborated clean while the same `arr.sort();` one level up
// was reported.
//
// Stmt::for_inits gets no case. A.6.8 admits only a
// list_of_variable_assignments or a for_variable_declaration there, and A.6.2
// gives `variable_assignment ::= variable_lvalue = expression`, so a
// for-loop initialization holds an assignment and never a bare
// function_subroutine_call; an ordering method returns no value, so it cannot
// stand in the expression of one either. Stmt::for_steps does get a case,
// because A.6.8 names function_subroutine_call among the for_step_assignment
// alternatives.
TEST(ArrayOrderingElaboration, SortOnAssocArrayInForkArmIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial begin\n"
      "    fork\n"
      "      arr.sort();\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'sort' cannot be applied to "
                            "associative array 'arr'",
                            5, "7.12.2"));
}

TEST(ArrayOrderingElaboration, SortOnAssocArrayInForStepIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 0; arr.sort()) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'sort' cannot be applied to "
                            "associative array 'arr'",
                            4, "7.12.2"));
}

// A.6.10 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, which is Stmt::assert_pass_stmt here and
// Stmt::assert_fail_stmt below.
TEST(ArrayOrderingElaboration, SortOnAssocArrayInAssertPassIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial assert (1) arr.sort();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'sort' cannot be applied to "
                            "associative array 'arr'",
                            3, "7.12.2"));
}

TEST(ArrayOrderingElaboration, SortOnAssocArrayInAssertFailIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial assert (1) else arr.sort();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'sort' cannot be applied to "
                            "associative array 'arr'",
                            3, "7.12.2"));
}

// §18.16 and A.6.7 give `randcase_item ::= expression : statement_or_null`.
TEST(ArrayOrderingElaboration, SortOnAssocArrayInRandcaseItemIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial begin\n"
      "    randcase\n"
      "      1: arr.sort();\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'sort' cannot be applied to "
                            "associative array 'arr'",
                            5, "7.12.2"));
}

// §18.17 and A.6.12 give `rs_code_block ::= { { data_declaration } {
// statement_or_null } }`.
TEST(ArrayOrderingElaboration, SortOnAssocArrayInRandsequenceCodeBlockIsError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int arr [string];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { arr.sort(); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array ordering method 'sort' cannot be applied to "
                            "associative array 'arr'",
                            5, "7.12.2"));
}

}  // namespace
