

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(UnpackedArrayConcatSim, TypedAssignPatternInArrayConcat) {
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

TEST(UnpackedArrayConcatSim, UnpackedArrayConcatInAssignPattern) {
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

TEST(UnpackedArrayConcatSim, VectorConcatInByteArrayConcat) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte BA[2];\n"
      "  initial BA = {{4'h0, 4'h6}, {4'h0, 4'hf}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* ba0 = f.ctx.FindVariable("BA[0]");
  auto* ba1 = f.ctx.FindVariable("BA[1]");
  ASSERT_NE(ba0, nullptr);
  ASSERT_NE(ba1, nullptr);
  EXPECT_EQ(ba0->value.ToUint64(), 6u);
  EXPECT_EQ(ba1->value.ToUint64(), 15u);
}

}  // namespace
