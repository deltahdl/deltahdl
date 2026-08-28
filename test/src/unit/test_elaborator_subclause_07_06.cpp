#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ArrayAssignmentValidation, ArrayAssignCompatibleTypes) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int a[4], b[4];\n"
             "  assign a = b;\n"
             "endmodule\n"));
}

TEST(ArrayAssignmentValidation, ArrayAssignSizeMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[4], b[8];\n"
      "  assign a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array size mismatch: 'a' has 4 elements but 'b' "
                            "has 8",
                            3, "7.6"));
}

TEST(ArrayAssignmentValidation, ArrayAssignTypeMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[4];\n"
      "  logic [31:0] b[4];\n"
      "  assign a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array element type mismatch in assignment "
                            "('a' vs 'b')",
                            4, "7.6"));
}

// §7.6: element types of source and target shall be equivalent. Two packed
// vector elements of the same 4-state kind but different widths are not
// equivalent, so the array assignment is rejected (a width-based negative,
// distinct from the signedness/state mismatch above).
TEST(ArrayAssignmentValidation, ElementWidthMismatchRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic [7:0]  a[4];\n"
      "  logic [15:0] b[4];\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array element type mismatch in assignment "
                            "('a' vs 'b')",
                            4, "7.6"));
}

TEST(ArrayAssignmentValidation, WireToVarArrayAssign) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] v[4];\n"
             "  wire [7:0] w[4];\n"
             "  assign w = v;\n"
             "endmodule\n"));
}

TEST(ArrayAssignmentValidation, WireSourceToVarTargetArrayAssign) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  wire [7:0] w[4];\n"
             "  logic [7:0] v[4];\n"
             "  initial v = w;\n"
             "endmodule\n"));
}

TEST(ArrayAssignmentValidation, DynamicToDynamicAssign) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int a[];\n"
             "  int b[];\n"
             "  initial a = b;\n"
             "endmodule\n"));
}

TEST(ArrayAssignmentValidation, PackedArrayContinuousAssign) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [15:0] a;\n"
             "  logic [15:0] b;\n"
             "  assign a = b;\n"
             "endmodule\n"));
}

TEST(ArrayAssignmentValidation, FixedToDynamicAssign) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int a[4];\n"
             "  int b[];\n"
             "  initial b = a;\n"
             "endmodule\n"));
}

TEST(ArrayAssignmentValidation, VectorToPackedIgnoresTargetBounds) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [3:0]  narrow;\n"
             "  logic [31:0] wide;\n"
             "  initial begin\n"
             "    narrow = wide;\n"
             "    wide   = narrow;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ArrayAssignmentValidation, IntAndBitSignedArrayAssignmentAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int a[4];\n"
             "  bit signed [31:0] b[4];\n"
             "  initial a = b;\n"
             "endmodule\n"));
}

TEST(ArrayAssignmentValidation, ArrayAssignDimensionCountMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[4];\n"
      "  int b[4][3];\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array assignment requires the same number of "
                            "unpacked dimensions ('a' has 1, 'b' has 2)",
                            4, "7.6"));
}

TEST(ArrayAssignmentValidation, FasterVaryingDimSizeMismatchRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[2][3];\n"
      "  int b[2][4];\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "faster-varying array dimension size mismatch in "
                            "assignment ('a' dim 1 is 3, 'b' dim 1 is 4)",
                            4, "7.6"));
}

TEST(ArrayAssignmentValidation, FasterVaryingDimSizeMatchAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int a[2][3];\n"
             "  int b[2][3];\n"
             "  initial a = b;\n"
             "endmodule\n"));
}

// §7.6: only the slowest-varying dimension gets the weaker (kind-flexible)
// treatment; a faster-varying fixed dimension must still be equivalent even
// when the leftmost dimension is dynamic (and therefore run-time sized).
TEST(ArrayAssignmentValidation, FasterVaryingDimMismatchDynamicOuterRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[][3];\n"
      "  int b[][4];\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "faster-varying array dimension size mismatch in "
                            "assignment ('a' dim 1 is 3, 'b' dim 1 is 4)",
                            4, "7.6"));
}

TEST(ArrayAssignmentValidation, FasterVaryingDimMatchDynamicOuterAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int a[][3];\n"
             "  int b[][3];\n"
             "  initial a = b;\n"
             "endmodule\n"));
}

TEST(ArrayAssignmentValidation, PackedToUnpackedWithoutCastRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic [31:0] p;\n"
      "  int u[4];\n"
      "  initial u = p;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed array 'p' cannot be directly assigned to "
                            "unpacked array 'u' without an explicit cast",
                            4, "7.6"));
}

// §7.9.9 is the rule that catches this, not §7.6: an associative array and a
// non-associative one are rejected on their kinds before the §7.6 shape and
// element checks are reached, so the report names §7.9.9.
TEST(ArrayAssignmentValidation, AssocToFixedArrayAssignRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[string];\n"
      "  int fa[4];\n"
      "  assign fa = aa;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array cannot be assigned to or from a "
                            "non-associative array",
                            4, "7.9.9"));
}

// §7.9.9 again, with the associative array on the left-hand side.
TEST(ArrayAssignmentValidation, FixedArrayToAssocAssignRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[string];\n"
      "  int fa[4];\n"
      "  assign aa = fa;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array cannot be assigned to or from a "
                            "non-associative array",
                            4, "7.9.9"));
}

// §7.9.9 again, with a dynamic array as the non-associative operand.
TEST(ArrayAssignmentValidation, AssocToDynamicArrayAssignRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  int da[];\n"
      "  assign da = aa;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array cannot be assigned to or from a "
                            "non-associative array",
                            4, "7.9.9"));
}

// §7.9.9 again, with the associative array on the left-hand side and a dynamic
// array on the right.
TEST(ArrayAssignmentValidation, DynamicArrayToAssocAssignRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  int da[];\n"
      "  assign aa = da;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array cannot be assigned to or from a "
                            "non-associative array",
                            4, "7.9.9"));
}

// §7.6 states the shape and element-type compatibility an array assignment
// requires and conditions the rule on the two operands, not on the statement
// the assignment is written in. Elaborator::WalkStmtsForArrayAssign wrote out
// six of the thirteen statement links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states, so each source below
// elaborated clean while the same `a = b;` one level up was reported. The seven
// cases write it in the seven links the walk did not read.
TEST(ArrayAssignmentValidation, ArrayAssignInForkArmRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[4], b[8];\n"
      "  initial begin\n"
      "    fork\n"
      "      a = b;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array size mismatch: 'a' has 4 elements but 'b' "
                            "has 8",
                            5, "7.6"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...` and
// A.6.2 gives `variable_assignment ::= variable_lvalue = expression`, so an
// array-to-array assignment is a conforming for-loop initialization.
TEST(ArrayAssignmentValidation, ArrayAssignInForInitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[4], b[8];\n"
      "  integer i;\n"
      "  initial for (a = b; i < 0; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array size mismatch: 'a' has 4 elements but 'b' "
                            "has 8",
                            4, "7.6"));
}

// A.6.8 gives `for_step_assignment ::= operator_assignment | ...`, and the
// assignment operator of an operator_assignment may be `=`.
TEST(ArrayAssignmentValidation, ArrayAssignInForStepRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[4], b[8];\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 0; a = b) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array size mismatch: 'a' has 4 elements but 'b' "
                            "has 8",
                            4, "7.6"));
}

// A.6.10 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, which is two statement links rather than one:
// Stmt::assert_pass_stmt here and Stmt::assert_fail_stmt below.
TEST(ArrayAssignmentValidation, ArrayAssignInAssertPassRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[4], b[8];\n"
      "  initial assert (1) a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array size mismatch: 'a' has 4 elements but 'b' "
                            "has 8",
                            3, "7.6"));
}

TEST(ArrayAssignmentValidation, ArrayAssignInAssertFailRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[4], b[8];\n"
      "  initial assert (1) else a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array size mismatch: 'a' has 4 elements but 'b' "
                            "has 8",
                            3, "7.6"));
}

// §18.16 and A.6.7 give `randcase_item ::= expression : statement_or_null`, and
// the parser puts that statement in the second of each Stmt::randcase_items
// pair.
TEST(ArrayAssignmentValidation, ArrayAssignInRandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[4], b[8];\n"
      "  initial begin\n"
      "    randcase\n"
      "      1: a = b;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array size mismatch: 'a' has 4 elements but 'b' "
                            "has 8",
                            5, "7.6"));
}

// §18.17 and A.6.12 give `rs_code_block ::= { { data_declaration } {
// statement_or_null } }`, so a production code block holds procedural
// statements like any other block.
TEST(ArrayAssignmentValidation, ArrayAssignInRandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[4], b[8];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { a = b; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array size mismatch: 'a' has 4 elements but 'b' "
                            "has 8",
                            5, "7.6"));
}

}  // namespace
