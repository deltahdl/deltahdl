#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA25, UnsizedDimWithInitInferSize) {
  ElabFixture f;
  auto* design = Elaborate("module m; int d [] = '{1,2,3}; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_dynamic);
  EXPECT_EQ(mod->variables[0].unpacked_size, 3u);
}

// §7.6: Compatible array types in continuous assignment — OK.
TEST(Elaboration, ArrayAssignCompatibleTypes) {
  EXPECT_TRUE(ElabOk(
      "module t;\n"
      "  int a[4], b[4];\n"
      "  assign a = b;\n"
      "endmodule\n"));
}

// §7.6: Fixed-size array size mismatch — error.
TEST(Elaboration, ArrayAssignSizeMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[4], b[8];\n"
      "  assign a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.6: Array element type mismatch — error.
TEST(Elaboration, ArrayAssignTypeMismatch) {
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

// §7.6: Same element type, same size — no error.
TEST(Elaboration, ArrayAssignSameTypeSameSize) {
  EXPECT_TRUE(ElabOk(
      "module t;\n"
      "  logic [7:0] a[10], b[10];\n"
      "  assign a = b;\n"
      "endmodule\n"));
}

// §7.6: Packed array treated as vector — vector to packed array is OK.
TEST(Elaboration, PackedArrayVectorAssign) {
  EXPECT_TRUE(ElabOk(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  assign a = b;\n"
      "endmodule\n"));
}

// §7.6: Wire-to-variable assignment compatibility.
TEST(Elaboration, WireToVarArrayAssign) {
  EXPECT_TRUE(ElabOk(
      "module t;\n"
      "  logic [7:0] v[4];\n"
      "  wire [7:0] w[4];\n"
      "  assign w = v;\n"
      "endmodule\n"));
}

// §11.2.2: Unpacked array data objects can be used as aggregate expressions.
TEST(AggregateExpr, UnpackedArrayAssignment) {
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

}  // namespace
