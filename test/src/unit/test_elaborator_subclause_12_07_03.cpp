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

}  // namespace
