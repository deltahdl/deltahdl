#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ArrayOperationValidation, ArrayAssignCompatibleTypes) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int a[4], b[4];\n"
             "  assign a = b;\n"
             "endmodule\n"));
}

TEST(ArrayOperationValidation, ArrayAssignSizeMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[4], b[8];\n"
      "  assign a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ArrayOperationValidation, ArrayAssignTypeMismatch) {
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

TEST(ArrayOperationValidation, ArrayAssignSameTypeSameSize) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] a[10], b[10];\n"
             "  assign a = b;\n"
             "endmodule\n"));
}

TEST(ArrayOperationValidation, PackedArrayVectorAssign) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] a;\n"
             "  logic [7:0] b;\n"
             "  assign a = b;\n"
             "endmodule\n"));
}

TEST(ArrayOperationValidation, WireToVarArrayAssign) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] v[4];\n"
             "  wire [7:0] w[4];\n"
             "  assign w = v;\n"
             "endmodule\n"));
}

TEST(ArrayOperationValidation, UnpackedArrayAssignment) {
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

TEST(ArrayOperationValidation, ArrayEqualityComparison) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a [4];\n"
      "  int b [4];\n"
      "  logic eq;\n"
      "  initial eq = (a == b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArrayOperationValidation, ArrayInequalityComparison) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a [4];\n"
      "  int b [4];\n"
      "  logic neq;\n"
      "  initial neq = (a != b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArrayOperationValidation, PackedArrayIntegerAssign) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] a;\n"
             "  initial a = 8'hFF;\n"
             "endmodule\n"));
}

TEST(ArrayOperationValidation, PackedArrayArithmeticExpression) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] a;\n"
             "  logic [7:0] b;\n"
             "  initial b = a + 8'd3;\n"
             "endmodule\n"));
}

TEST(ArrayOperationValidation, AssocArraySliceRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  initial x = aa[0+:2];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
