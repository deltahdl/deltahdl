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

TEST(ArrayAssignmentValidation, WireToVarArrayAssign) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] v[4];\n"
             "  wire [7:0] w[4];\n"
             "  assign w = v;\n"
             "endmodule\n"));
}

TEST(ArrayAssignmentValidation, UnpackedArrayAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a [4];\n"
      "  int b [4];\n"
      "  initial b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
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

// §7.6: "Any vector expression can be assigned to any packed array. The
// packed array bounds of the target packed array do not affect the
// assignment." Verify a wider/narrower vector → packed target elaborates.
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

// §7.6: "Associative arrays are assignment compatible only with associative
// arrays." Cross-kind assignment between an associative and a non-associative
// unpacked array must be rejected by the elaborator.
TEST(ArrayAssignmentValidation, AssocCannotAssignToNonAssoc) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int aa[string];\n"
      "  int a[4];\n"
      "  initial a = aa;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.6: "The element types of source and target shall be equivalent."
// §7.6 defers element equivalence to §6.22.2 rule (c): integral elements with
// the same width, signedness, and state are equivalent even when their kinds
// differ. `int` and `bit signed [31:0]` both denote a 32-bit, signed, 2-state
// element, so element-wise array assignment shall elaborate.
TEST(ArrayAssignmentValidation, IntAndBitSignedArrayAssignmentAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int a[4];\n"
             "  bit signed [31:0] b[4];\n"
             "  initial a = b;\n"
             "endmodule\n"));
}

// §7.6: "for two arrays to be assignment compatible it is necessary that they
// have the same number of unpacked dimensions."
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

// §7.6: "A packed array cannot be directly assigned to an unpacked array
// without an explicit cast." Assigning the bare packed source `p` to the
// unpacked target `u` shall be rejected at elaboration.
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

// §7.6: "Associative arrays are assignment compatible only with associative
// arrays." Each cross-kind direction must be rejected by the elaborator.
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
