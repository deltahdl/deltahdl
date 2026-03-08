// §10.10.3

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// §10.10.3: Typed assignment pattern element in unpacked array concat
// produces correct values.
TEST(SimCh10j, TypedAssignPatternInArrayConcat) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3 = '{1, 2, 3};\n"
      "  int A9[1:9];\n"
      "  initial A9 = {A3, 4, AI3'{5, 6, 7}, 8, 9};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  for (int i = 1; i <= 9; ++i) {
    auto name = "A9[" + std::to_string(i) + "]";
    auto* var = f.ctx.FindVariable(name);
    ASSERT_NE(var, nullptr) << name;
    EXPECT_EQ(var->value.ToUint64(), static_cast<uint64_t>(i)) << name;
  }
}

// §10.10.3: Unpacked array concat as item in assignment pattern
// builds a correct 2D array.
TEST(SimCh10j, UnpackedArrayConcatInAssignPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int C[2][2];\n"
      "  initial C = '{{1, 2}, {3, 4}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* c00 = f.ctx.FindVariable("C[0][0]");
  auto* c01 = f.ctx.FindVariable("C[0][1]");
  auto* c10 = f.ctx.FindVariable("C[1][0]");
  auto* c11 = f.ctx.FindVariable("C[1][1]");
  ASSERT_NE(c00, nullptr);
  ASSERT_NE(c01, nullptr);
  ASSERT_NE(c10, nullptr);
  ASSERT_NE(c11, nullptr);
  EXPECT_EQ(c00->value.ToUint64(), 1u);
  EXPECT_EQ(c01->value.ToUint64(), 2u);
  EXPECT_EQ(c10->value.ToUint64(), 3u);
  EXPECT_EQ(c11->value.ToUint64(), 4u);
}

// §10.10.3: Scalar and array items mixed in unpacked array concat
// all have self-determined types and evaluate correctly.
TEST(SimCh10j, MixedSelfDeterminedItems) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[0:1] = '{10, 20};\n"
      "  int B[0:3];\n"
      "  initial B = {A, 30, 40};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* b0 = f.ctx.FindVariable("B[0]");
  auto* b1 = f.ctx.FindVariable("B[1]");
  auto* b2 = f.ctx.FindVariable("B[2]");
  auto* b3 = f.ctx.FindVariable("B[3]");
  ASSERT_NE(b0, nullptr);
  ASSERT_NE(b1, nullptr);
  ASSERT_NE(b2, nullptr);
  ASSERT_NE(b3, nullptr);
  EXPECT_EQ(b0->value.ToUint64(), 10u);
  EXPECT_EQ(b1->value.ToUint64(), 20u);
  EXPECT_EQ(b2->value.ToUint64(), 30u);
  EXPECT_EQ(b3->value.ToUint64(), 40u);
}

}  // namespace
