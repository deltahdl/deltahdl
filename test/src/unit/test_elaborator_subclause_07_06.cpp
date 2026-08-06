#include "fixture_elaborator.h"

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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
