// Non-LRM tests

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// §10.10.1: Unpacked array concat vs assignment pattern produce the same
// result.
TEST(SimCh10j, ConcatAndPatternEquivalent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A [1:3];\n"
      "  int B [1:3];\n"
      "  initial begin\n"
      "    A = {1, 2, 3};\n"
      "    B = '{1, 2, 3};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  for (int i = 1; i <= 3; ++i) {
    auto a_name = "A[" + std::to_string(i) + "]";
    auto b_name = "B[" + std::to_string(i) + "]";
    auto* a = f.ctx.FindVariable(a_name);
    auto* b = f.ctx.FindVariable(b_name);
    ASSERT_NE(a, nullptr) << a_name;
    ASSERT_NE(b, nullptr) << b_name;
    EXPECT_EQ(a->value.ToUint64(), b->value.ToUint64()) << "index " << i;
  }
}

// §10.10: Unpacked array concatenation from scalar elements.
TEST(SimCh10j, UnpackedArrayConcatScalarElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:2];\n"
      "  initial begin\n"
      "    arr = {1, 2, 3};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  auto* e2 = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 1u);
  EXPECT_EQ(e1->value.ToUint64(), 2u);
  EXPECT_EQ(e2->value.ToUint64(), 3u);
}

// §10.10: Basic unpacked array concatenation elaborates.
TEST(UnpackedArrayConcatElaborates, UnpackedArrayConcatElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[3];\n"
      "  initial A = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// §10.10: Array items in unpacked array concatenation elaborate.
TEST(ArrayItemExpansionElaborates, ArrayItemExpansionElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[2], B[2], C[4];\n"
      "  initial C = {A, B};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// §10.10: Array item expansion in unpacked array concatenation.
TEST(UnpackedArrayConcatArrayExpansion, UnpackedArrayConcatArrayExpansion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A [0:1] = '{10, 20};\n"
      "  int B [0:1] = '{30, 40};\n"
      "  int C [0:3];\n"
      "  initial begin\n"
      "    C = {A, B};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* c0 = f.ctx.FindVariable("C[0]");
  auto* c1 = f.ctx.FindVariable("C[1]");
  auto* c2 = f.ctx.FindVariable("C[2]");
  auto* c3 = f.ctx.FindVariable("C[3]");
  ASSERT_NE(c0, nullptr);
  ASSERT_NE(c1, nullptr);
  ASSERT_NE(c2, nullptr);
  ASSERT_NE(c3, nullptr);
  EXPECT_EQ(c0->value.ToUint64(), 10u);
  EXPECT_EQ(c1->value.ToUint64(), 20u);
  EXPECT_EQ(c2->value.ToUint64(), 30u);
  EXPECT_EQ(c3->value.ToUint64(), 40u);
}

// §10.10: Mixed scalar and array items in unpacked array concatenation.
TEST(UnpackedArrayConcatMixed, UnpackedArrayConcatMixed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A [0:1] = '{1, 2};\n"
      "  int B [0:2];\n"
      "  initial begin\n"
      "    B = {A, 3};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* b0 = f.ctx.FindVariable("B[0]");
  auto* b1 = f.ctx.FindVariable("B[1]");
  auto* b2 = f.ctx.FindVariable("B[2]");
  ASSERT_NE(b0, nullptr);
  ASSERT_NE(b1, nullptr);
  ASSERT_NE(b2, nullptr);
  EXPECT_EQ(b0->value.ToUint64(), 1u);
  EXPECT_EQ(b1->value.ToUint64(), 2u);
  EXPECT_EQ(b2->value.ToUint64(), 3u);
}

// §10.10: Unpacked array concatenation with descending-range target.
TEST(UnpackedArrayConcatDescending, UnpackedArrayConcatDescending) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [2:0];\n"
      "  initial begin\n"
      "    arr = {10, 20, 30};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  auto* e2 = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  EXPECT_EQ(e2->value.ToUint64(), 10u);
  EXPECT_EQ(e1->value.ToUint64(), 20u);
  EXPECT_EQ(e0->value.ToUint64(), 30u);
}

}  // namespace
