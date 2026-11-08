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
