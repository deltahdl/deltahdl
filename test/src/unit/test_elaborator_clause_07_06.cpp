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

TEST(ArrayAssignmentValidation, ArrayAssignSameTypeSameSize) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] a[10], b[10];\n"
             "  assign a = b;\n"
             "endmodule\n"));
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

}  // namespace
