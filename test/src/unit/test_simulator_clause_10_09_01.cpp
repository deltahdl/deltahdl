#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ArrayLiteralSim, PositionalAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2];\n"
      "  initial arr = '{8'hAA, 8'hBB, 8'hCC};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xAA);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xBB);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xCC);
}

TEST(ArrayLiteralSim, PositionalVarInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{8'h11, 8'h22, 8'h33};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x11);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x22);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x33);
}

TEST(ArrayLiteralSim, ReplicationAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2];\n"
      "  initial arr = '{3{8'hFF}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xFF);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xFF);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xFF);
}

TEST(ArrayLiteralSim, ReplicationVarInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{3{8'hAA}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xAA);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xAA);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xAA);
}

TEST(ArrayLiteralSim, DefaultAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2];\n"
      "  initial arr = '{default: 8'h42};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x42);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x42);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x42);
}

TEST(ArrayLiteralSim, DefaultVarInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{default: 8'h99};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x99);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x99);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x99);
}

TEST(ArrayLiteralSim, IndexKeyWithDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2];\n"
      "  initial arr = '{1: 8'hBB, default: 8'h00};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x00);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xBB);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x00);
}

TEST(ArrayLiteralSim, IndexKeyVarInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{2: 8'hCC, default: 8'h11};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x11);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x11);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xCC);
}

TEST(ArrayLiteralSim, DescendingRange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [2:0] = '{8'hAA, 8'hBB, 8'hCC};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xAA);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xBB);
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xCC);
}

TEST(ArrayLiteralSim, PositionalPatternInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:1];\n"
      "  initial begin\n"
      "    arr = '{10, 20};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 10u);
  EXPECT_EQ(e1->value.ToUint64(), 20u);
}

TEST(ArrayLiteralSim, MultipleIndexKeysWithDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:2];\n"
      "  initial begin\n"
      "    arr = '{0: 100, 2: 200, default: 0};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  auto* e2 = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 100u);
  EXPECT_EQ(e1->value.ToUint64(), 0u);
  EXPECT_EQ(e2->value.ToUint64(), 200u);
}

TEST(ArrayLiteralSim, DescendingRangeAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [1:0];\n"
      "  initial begin\n"
      "    arr = '{30, 40};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e1->value.ToUint64(), 30u);
  EXPECT_EQ(e0->value.ToUint64(), 40u);
}

TEST(ArrayLiteralSim, VarDeclPatternInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:2] = '{5, 10, 15};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  auto* e2 = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 5u);
  EXPECT_EQ(e1->value.ToUint64(), 10u);
  EXPECT_EQ(e2->value.ToUint64(), 15u);
}

TEST(ArrayLiteralSim, ReplicationMultiElement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [0:3];\n"
      "  initial arr = '{2{5, 10}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  auto* e2 = f.ctx.FindVariable("arr[2]");
  auto* e3 = f.ctx.FindVariable("arr[3]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  ASSERT_NE(e3, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 5u);
  EXPECT_EQ(e1->value.ToUint64(), 10u);
  EXPECT_EQ(e2->value.ToUint64(), 5u);
  EXPECT_EQ(e3->value.ToUint64(), 10u);
}

TEST(ArrayLiteralSim, SingleElementInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [0:0] = '{42};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  ASSERT_NE(e0, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 42u);
}

TEST(ArrayLiteralSim, IndexKeyOnlyAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [0:2];\n"
      "  initial arr = '{0: 10, 1: 20, 2: 30};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  auto* e2 = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 10u);
  EXPECT_EQ(e1->value.ToUint64(), 20u);
  EXPECT_EQ(e2->value.ToUint64(), 30u);
}

TEST(ArrayLiteralSim, NarrowToWideContextEval) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [0:1];\n"
      "  initial arr = '{1'b1, 1'b1};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 1u);
  EXPECT_EQ(e1->value.ToUint64(), 1u);
}

TEST(ArrayLiteralSim, WideToNarrowContextEval) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] arr [0:1];\n"
      "  initial arr = '{8'hAB, 8'hCD};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 0xBu);
  EXPECT_EQ(e1->value.ToUint64(), 0xDu);
}

TEST(ArrayLiteralSim, PositionalMultidimensionalValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [0:1][0:1];\n"
      "  initial arr = '{'{1, 2}, '{3, 4}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e00 = f.ctx.FindVariable("arr[0][0]");
  auto* e01 = f.ctx.FindVariable("arr[0][1]");
  auto* e10 = f.ctx.FindVariable("arr[1][0]");
  auto* e11 = f.ctx.FindVariable("arr[1][1]");
  ASSERT_NE(e00, nullptr);
  ASSERT_NE(e01, nullptr);
  ASSERT_NE(e10, nullptr);
  ASSERT_NE(e11, nullptr);
  EXPECT_EQ(e00->value.ToUint64(), 1u);
  EXPECT_EQ(e01->value.ToUint64(), 2u);
  EXPECT_EQ(e10->value.ToUint64(), 3u);
  EXPECT_EQ(e11->value.ToUint64(), 4u);
}

TEST(ArrayLiteralSim, DefaultMultidimensionalValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [0:1][0:1];\n"
      "  initial arr = '{default: '{default: 42}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e00 = f.ctx.FindVariable("arr[0][0]");
  auto* e01 = f.ctx.FindVariable("arr[0][1]");
  auto* e10 = f.ctx.FindVariable("arr[1][0]");
  auto* e11 = f.ctx.FindVariable("arr[1][1]");
  ASSERT_NE(e00, nullptr);
  ASSERT_NE(e01, nullptr);
  ASSERT_NE(e10, nullptr);
  ASSERT_NE(e11, nullptr);
  EXPECT_EQ(e00->value.ToUint64(), 42u);
  EXPECT_EQ(e01->value.ToUint64(), 42u);
  EXPECT_EQ(e10->value.ToUint64(), 42u);
  EXPECT_EQ(e11->value.ToUint64(), 42u);
}

}  // namespace
