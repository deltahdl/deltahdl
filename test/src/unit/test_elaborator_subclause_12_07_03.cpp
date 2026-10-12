#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(LoopStatementElaboration, ForeachLoop) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [4];\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    foreach (arr[i]) total = total + arr[i];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForeachMultiDimElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] matrix [0:3][0:3];\n"
      "  initial begin\n"
      "    foreach (matrix[i, j]) matrix[i][j] = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.7.3 — the number of loop variables shall not exceed the number of array
// dimensions.
TEST(LoopStatementElaboration, ForeachTooManyLoopVarsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i, j]) arr[i] = j;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'arr' has only 1 dimension(s)",
      4, "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachLoopVarCountAtDimLimitOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i, j]) arr[i][j] = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.7.3 — foreach loop variables are read-only.
TEST(LoopStatementElaboration, ForeachLoopVarAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) i = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            4, "12.7.3"));
}

// §12.7.3 declares the loop variable, so the assignment to it breaks the
// read-only rule and nothing else: the name resolves, and no §23.9 report of
// an undeclared identifier stands beside the read-only one.
TEST(LoopStatementElaboration, ForeachLoopVarAssignIsNotAnUndeclaredName) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) begin i = 0; arr[i] = 1; end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            4, "12.7.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'i'",
                             4, "23.9"));
}

TEST(LoopStatementElaboration, ForeachLoopVarIncrementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) i++;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            4, "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachAssignArrayElementOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) arr[i] = i;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.7.3 — the read-only rule applies regardless of the assignment form;
// a nonblocking assignment to a loop variable is just as illegal.
TEST(LoopStatementElaboration, ForeachLoopVarNonblockingAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) i <= 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            4, "12.7.3"));
}

// §12.7.3 — a loop variable may not reuse the array's identifier.
// §12.7.3 gives a loop variable over an associative array indexed by a
// specific type that index type, and a class handle is a reference to an
// object: a write to a member reached through the handle writes the object,
// so the read-only rule is not touched. UVM's uvm_phase.svh writes
// `pred.m_successors[begin_node] = 1;` inside `foreach (m_predecessors[pred])`.
TEST(LoopStatementElaboration, ForeachLoopVarMemberWriteThroughHandleOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class node;\n"
      "  int count;\n"
      "endclass\n"
      "module m;\n"
      "  bit preds [node];\n"
      "  initial begin\n"
      "    foreach (preds[p]) p.count = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration,
     ForeachLoopVarMemberElementWriteThroughHandleOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class node;\n"
      "  bit succ [node];\n"
      "endclass\n"
      "module m;\n"
      "  bit preds [node];\n"
      "  node q;\n"
      "  initial begin\n"
      "    foreach (preds[p]) p.succ[q] = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.7.1 has a for loop that declares its control variables create an
// implicit block around itself, and §6.21 makes a variable declared in a block
// local to it and the blocks nested below: an inner declaration of the loop
// variable's name is another variable, and writes to that name inside its
// scope are not writes to the loop variable. UVM's uvm_reg.svh writes
// `for (int i = f.get_lsb_pos(); i < top; i++)` inside `foreach (m_fields[i])`.
TEST(LoopStatementElaboration, ForeachLoopVarRedeclaredByInnerForLoopOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) for (int i = 0; i < 2; i++) arr[i] = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForeachLoopVarRedeclaredInInnerBlockOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) begin\n"
      "      int i;\n"
      "      i = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A for loop whose initialization assigns without declaring writes the loop
// variable itself.
TEST(LoopStatementElaboration, ForeachLoopVarAssignedByInnerForInitIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) for (i = 0; i < 2; i++) arr[i] = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            4, "12.7.3"));
}

// The inner for loop's variable is local to that loop: after it, the name is
// the loop variable again.
TEST(LoopStatementElaboration, ForeachLoopVarAssignedAfterInnerForLoopIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) begin\n"
      "      for (int i = 0; i < 2; i++) arr[i] = 0;\n"
      "      i = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            6, "12.7.3"));
}

// A bit-select of the loop variable itself is still a write to it.
TEST(LoopStatementElaboration, ForeachLoopVarBitSelectAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) i[0] = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            4, "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachLoopVarSameNameAsArrayIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  int x;\n"
      "  initial begin\n"
      "    foreach (arr[arr]) x = arr;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'arr' may not have the same "
                            "name as the array it iterates over",
                            5, "12.7.3"));
}

// §12.7.3 — the identifier-clash rule covers every loop-variable slot, not
// just the first one.
TEST(LoopStatementElaboration, ForeachLaterLoopVarSameNameAsArrayIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] matrix [0:3][0:3];\n"
      "  int x;\n"
      "  initial begin\n"
      "    foreach (matrix[i, matrix]) x = i;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'matrix' may not have the "
                            "same name as the array it iterates over",
                            5, "12.7.3"));
}

// §12.7.3 makes a foreach loop variable read-only for the whole of the loop
// body and caps the loop-variable count at the array's dimensionality, and it
// puts no condition on which statement the foreach or the offending assignment
// is written inside. So every member of Stmt that holds a statement is a
// position both rules reach.
//
// CheckForeachVarsReadOnly and CheckForeachInStmt in
// src/elaborator/elaborator_validate_funcchecks.cpp each enumerated nine of the
// thirteen members, and now take the list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h instead. The ten cases below
// cover the four members neither walk reached: Stmt::assert_pass_stmt,
// Stmt::assert_fail_stmt, Stmt::randcase_items and Stmt::rs_productions, the
// last counted twice because a randsequence production holds statements in two
// separate lists. Five hold the read-only rule to those positions and five hold
// the dimension rule to them, because a walk can gain a member for one rule
// without gaining it for the other.

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each, because a walk reaches one member without the other.
TEST(LoopStatementElaboration,
     ForeachLoopVarAssignedInAnAssertionPassStatementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  logic ok;\n"
      "  initial foreach (arr[i]) assert (ok) i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            4, "12.7.3"));
}

TEST(LoopStatementElaboration,
     ForeachLoopVarAssignedInAnAssertionFailStatementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  logic ok;\n"
      "  initial foreach (arr[i]) assert (ok) else i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            4, "12.7.3"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, kept in
// Stmt::randcase_items. §12.7.3 is a rule about the source, so it holds whether
// the weighted draw would select the item or not.
TEST(LoopStatementElaboration, ForeachLoopVarAssignedInARandcaseItemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial foreach (arr[i]) randcase 1: i = 1; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            3, "12.7.3"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(LoopStatementElaboration,
     ForeachLoopVarAssignedInARandsequenceCodeBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial foreach (arr[i]) begin\n"
      "    randsequence(main)\n"
      "      main : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            5, "12.7.3"));
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second list under
// Stmt::rs_productions, so a walk reaches it without reaching
// RsProd::code_stmts and the case above does not answer for it. The other
// production writes j, so the report this case reads is the weight block's.
TEST(LoopStatementElaboration,
     ForeachLoopVarAssignedInARandsequenceWeightCodeBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  int j;\n"
      "  initial foreach (arr[i]) begin\n"
      "    randsequence(main)\n"
      "      main : a := 1 { i = 1; };\n"
      "      a : { j = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            6, "12.7.3"));
}

// The dimension rule in the same four positions. Each source declares arr with
// one dimension and writes two loop variables, so the report names the foreach
// under test and nothing else in the source can produce it.
TEST(LoopStatementElaboration,
     ForeachInAnAssertionPassStatementIsHeldToTheArrayDimensionCount) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  logic ok;\n"
      "  initial assert (ok) foreach (arr[i, j]) arr[i] = j;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'arr' has only 1 dimension(s)",
      4, "12.7.3"));
}

TEST(LoopStatementElaboration,
     ForeachInAnAssertionFailStatementIsHeldToTheArrayDimensionCount) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  logic ok;\n"
      "  initial assert (ok) else foreach (arr[i, j]) arr[i] = j;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'arr' has only 1 dimension(s)",
      4, "12.7.3"));
}

TEST(LoopStatementElaboration,
     ForeachInARandcaseItemIsHeldToTheArrayDimensionCount) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial randcase 1: foreach (arr[i, j]) arr[i] = j; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'arr' has only 1 dimension(s)",
      3, "12.7.3"));
}

TEST(LoopStatementElaboration,
     ForeachInARandsequenceCodeBlockIsHeldToTheArrayDimensionCount) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { foreach (arr[i, j]) arr[i] = j; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'arr' has only 1 dimension(s)",
      5, "12.7.3"));
}

// The other production writes k with no foreach, so the report this case reads
// is the weight block's.
TEST(LoopStatementElaboration,
     ForeachInARandsequenceWeightCodeBlockIsHeldToTheArrayDimensionCount) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  int k;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := 1 { foreach (arr[i, j]) arr[i] = j; };\n"
      "      a : { k = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'arr' has only 1 dimension(s)",
      6, "12.7.3"));
}

// §12.7.3 caps a foreach's loop variables at its array's dimension count
// wherever the array is declared. The arrays below are declared in a block, in
// a function, as a function's formal and as a class property, and each foreach
// names one loop variable more than its array has dimensions.
TEST(LoopStatementElaboration, ForeachOverBlockLocalArrayCountsItsDimensions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    int a [4];\n"
      "    foreach (a[i, j, k]) begin end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 3 loop variables but array 'a' has only 1 dimension(s)", 4,
      "12.7.3"));
}

TEST(LoopStatementElaboration,
     ForeachOverFunctionLocalArrayCountsItsDimensions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    int a [4];\n"
      "    foreach (a[i, j]) begin end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'a' has only 1 dimension(s)", 4,
      "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachOverFormalArrayCountsItsDimensions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f(int a [4]);\n"
      "    foreach (a[i, j]) begin end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'a' has only 1 dimension(s)", 3,
      "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachOverClassPropertyCountsItsDimensions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class C;\n"
      "    int a [4];\n"
      "    function void f();\n"
      "      foreach (a[i, j]) begin end\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'a' has only 1 dimension(s)", 5,
      "12.7.3"));
}

// A class of the compilation unit, declared outside every module, has its
// properties in scope in its methods as a module's class has.
TEST(LoopStatementElaboration,
     ForeachOverAUnitClassPropertyCountsItsDimensions) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  int a [4];\n"
      "  function void f();\n"
      "    foreach (a[i, j]) begin end\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'a' has only 1 dimension(s)", 4,
      "12.7.3"));
}

// The array a foreach names is the declaration in scope where the loop stands:
// the block's one-dimensional a hides the module's two-dimensional a, so two
// loop variables are one too many.
TEST(LoopStatementElaboration, ForeachCountsTheArrayItsBlockDeclares) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a [4][4];\n"
      "  initial begin\n"
      "    int a [4];\n"
      "    foreach (a[i, j]) begin end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'a' has only 1 dimension(s)", 5,
      "12.7.3"));
}

// The other way round, the block's two-dimensional a takes two loop variables
// though the module's a has one dimension.
TEST(LoopStatementElaboration, ForeachOverBlockArrayHidingAModuleArrayOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a [4];\n"
      "  initial begin\n"
      "    int a [4][4];\n"
      "    foreach (a[i, j]) begin end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// An array of real or string has its unpacked dimensions alone, the element
// type having no packed dimension, so §12.7.3's count is known from the
// declaration as it is for an integral array.
TEST(LoopStatementElaboration, ForeachOverRealArrayCountsItsDimensions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r [4];\n"
      "  initial foreach (r[i, j]) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'r' has only 1 dimension(s)", 3,
      "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachOverStringArrayCountsItsDimensions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string s [2][3];\n"
      "  initial foreach (s[i, j, k]) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 3 loop variables but array 's' has only 2 dimension(s)", 3,
      "12.7.3"));
}

// An array of class handles has its unpacked dimensions alone too, a handle
// being no packed array.
TEST(LoopStatementElaboration, ForeachOverClassHandleArrayCountsItsDimensions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class C; endclass\n"
      "  C h [4];\n"
      "  initial foreach (h[i, j]) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'h' has only 1 dimension(s)", 4,
      "12.7.3"));
}

// §12.7.3's loop variables are read-only, and an increment or an assignment
// operator written inside an expression writes its operand as surely as an
// assignment statement does (§11.4.1, §11.4.2).
TEST(LoopStatementElaboration, ForeachLoopVarWrittenInsideAnExpressionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a [4]; int x;\n"
      "  initial foreach (a[i]) begin\n"
      "    x = i++;\n"
      "    x = (i += 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* msg =
      "foreach loop variable 'i' is read-only and cannot be assigned";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 4, "12.7.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 5, "12.7.3"));
}

// An increment written as a whole statement is reported once, not once as a
// statement and again as an expression.
TEST(LoopStatementElaboration, ForeachLoopVarIncrementStatementReportedOnce) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a [4];\n"
      "  initial foreach (a[i]) i++;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach loop variable 'i' is read-only and cannot be assigned", 3,
      "12.7.3"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

// A subroutine writes the actual of an output, inout or ref formal (§13.5), so
// passing a loop variable there breaks §12.7.3's read-only rule; an input or a
// const ref formal only reads it.
TEST(LoopStatementElaboration, ForeachLoopVarPassedToAWritingFormalIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a [4];\n"
      "  task automatic t_out(output int v); v = 0; endtask\n"
      "  task automatic t_io(inout int v); v = 0; endtask\n"
      "  task automatic t_ref(ref int v); v = 0; endtask\n"
      "  initial foreach (a[i]) begin\n"
      "    t_out(i);\n"
      "    t_io(.v(i));\n"
      "    t_ref(i);\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* msg =
      "foreach loop variable 'i' is read-only and cannot be assigned";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 7, "12.7.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 8, "12.7.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 9, "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachLoopVarPassedToAReadingFormalOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a [4];\n"
      "  task automatic t_in(input int v); endtask\n"
      "  task automatic t_cref(const ref int v); endtask\n"
      "  int n;\n"
      "  initial foreach (a[i]) begin\n"
      "    t_in(i);\n"
      "    t_cref(i);\n"
      "    n = a.sum();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
