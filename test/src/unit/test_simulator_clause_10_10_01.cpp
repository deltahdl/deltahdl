

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(UnpackedArrayConcatSim, ConcatAndPatternEquivalent) {
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

TEST(UnpackedArrayConcatSim, UnpackedArrayConcatMixed) {
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

TEST(UnpackedArrayConcatSim, MixedArrayAndScalarItems) {
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

TEST(UnpackedArrayConcatSim, SameArrayUsedMultipleTimes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3 = '{1, 2, 3};\n"
      "  int A9[1:9];\n"
      "  initial A9 = {A3, 4, 5, A3, 6};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  uint64_t expected[] = {1, 2, 3, 4, 5, 1, 2, 3, 6};
  for (int i = 1; i <= 9; ++i) {
    auto name = "A9[" + std::to_string(i) + "]";
    auto* var = f.ctx.FindVariable(name);
    ASSERT_NE(var, nullptr) << name;
    EXPECT_EQ(var->value.ToUint64(), expected[i - 1]) << name;
  }
}

}  // namespace
