#include <gtest/gtest.h>

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

// §7.6 with §6.22.2: the element types of an array assignment are equivalent
// only when they match, for an enumeration or a class, never because two of
// them have the same width. A typedef renaming an enumeration matches it.
TEST(ArrayAssignmentValidation, EnumAndClassElementTypesComparedByIdentity) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum {A, B} e1_t;\n"
      "  typedef enum {C, D} e2_t;\n"
      "  class K; endclass\n"
      "  class M; endclass\n"
      "  e1_t x[2];\n"
      "  e2_t y[2];\n"
      "  K kx[2];\n"
      "  M my[2];\n"
      "  typedef e1_t e3_t;\n"
      "  e3_t z[2];\n"
      "  initial begin\n"
      "    x = y;\n"
      "    kx = my;\n"
      "    x = z;\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "array element type mismatch in assignment ('x' vs 'y')", 13,
      "7.6"));
  EXPECT_TRUE(ReportedError(
      diags, "array element type mismatch in assignment ('kx' vs 'my')", 14,
      "7.6"));
  for (const auto& d : diags) EXPECT_NE(d.loc.line, 15u) << d.message;
}

// §7.6: a subarray, an element of an array that is itself an array, and a
// slice are assignment compatible with another array only when their element
// types are equivalent and, the target being fixed-size or a slice, the counts
// agree. A slice whose bounds or width are not literals, or a subarray whose
// dimensions are not all of a fixed size, is not judged here.
TEST(ArrayAssignmentValidation, SlicesAndSubarraysAreJudged) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int N = 2;\n"
      "  int A[2][4];\n"
      "  int B[10];\n"
      "  int C[3];\n"
      "  logic [7:0] L[4];\n"
      "  int D[3][];\n"
      "  int E[2][3][];\n"
      "  int F[4];\n"
      "  initial begin\n"
      "    A[1] = C;\n"
      "    B[0:3] = C;\n"
      "    C = B[0:4];\n"
      "    A[0] = L;\n"
      "    C = B[2+:3];\n"
      "    C = B[4-:3];\n"
      "    C = B[0:N];\n"
      "    C = B[N:4];\n"
      "    C = B[1+:N];\n"
      "    D[1] = C;\n"
      "    E[1] = C;\n"
      "    F = A[1];\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "array size mismatch: 'A' has 4 elements but 'C' has 3", 11,
      "7.6"));
  EXPECT_TRUE(ReportedError(
      diags, "array size mismatch: 'B' has 4 elements but 'C' has 3", 12,
      "7.6"));
  EXPECT_TRUE(ReportedError(
      diags, "array size mismatch: 'C' has 3 elements but 'B' has 5", 13,
      "7.6"));
  EXPECT_TRUE(ReportedError(
      diags, "array element type mismatch in assignment ('A' vs 'L')", 14,
      "7.6"));
  for (const auto& d : diags) {
    EXPECT_FALSE(d.loc.line >= 15 && d.loc.line <= 22)
        << d.loc.line << ": " << d.message;
  }
}

// §7.6: a declaration assignment is an assignment to the variable declared,
// so an array initialized from another array is judged as an assignment of
// the same right-hand side would be.
TEST(ArrayAssignmentValidation, DeclarationInitializersAreJudged) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int B[4];\n"
      "  logic [7:0] L[3];\n"
      "  int A[3] = B;\n"
      "  int D[3] = L;\n"
      "  int E[4] = B;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "array size mismatch: 'A' has 3 elements but 'B' has 4", 4,
      "7.6"));
  EXPECT_TRUE(ReportedError(
      diags, "array element type mismatch in assignment ('D' vs 'L')", 5,
      "7.6"));
  for (const auto& d : diags) EXPECT_NE(d.loc.line, 6u) << d.message;
}

// §7.6 holds for an array a procedural block or a subroutine declares as for
// one among the module's items: in its declaration's initializer, in an
// assignment, and with a subroutine's arguments among the arrays. A block's
// declaration hides a module array of the same name.
TEST(ArrayAssignmentValidation, ArraysOfBlocksAndSubroutinesAreJudged) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int x[5];\n"
      "  initial begin\n"
      "    int a[3];\n"
      "    int b[4];\n"
      "    logic [7:0] l[3];\n"
      "    int c[3] = b;\n"
      "    int x[3];\n"
      "    int d[];\n"
      "    int q[$];\n"
      "    int m[string];\n"
      "    int z;\n"
      "    a = b;\n"
      "    a = l;\n"
      "    a = x;\n"
      "    d = b;\n"
      "    z = 1;\n"
      "    m = m;\n"
      "  end\n"
      "  task t(input int p[2]); int r[3]; r = p; endtask\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "array size mismatch: 'c' has 3 elements but 'b' has 4", 7,
      "7.6"));
  EXPECT_TRUE(ReportedError(
      diags, "array size mismatch: 'a' has 3 elements but 'b' has 4", 13,
      "7.6"));
  EXPECT_TRUE(ReportedError(
      diags, "array element type mismatch in assignment ('a' vs 'l')", 14,
      "7.6"));
  EXPECT_TRUE(ReportedError(
      diags, "array size mismatch: 'r' has 3 elements but 'p' has 2", 20,
      "7.6"));
  for (const auto& d : diags) {
    EXPECT_FALSE(d.loc.line >= 15 && d.loc.line <= 18)
        << d.loc.line << ": " << d.message;
  }
}

// §7.6 with §6.22.2: an enumeration is equivalent only to a type matching it,
// so an array of int and an array of an enumeration are not assignment
// compatible in either direction, however wide the enumeration's base is.
TEST(ArrayAssignmentValidation, IntAndEnumElementsAreNotEquivalent) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum {A, B} e_t;\n"
      "  e_t x[2];\n"
      "  int ia[2];\n"
      "  initial begin\n"
      "    ia = x;\n"
      "    x = ia;\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "array element type mismatch in assignment ('ia' vs 'x')", 6,
      "7.6"));
  EXPECT_TRUE(ReportedError(
      diags, "array element type mismatch in assignment ('x' vs 'ia')", 7,
      "7.6"));
}

}  // namespace
