#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

struct Array2x2 {
  Variable* e00 = nullptr;
  Variable* e01 = nullptr;
  Variable* e10 = nullptr;
  Variable* e11 = nullptr;
};

Array2x2 RunAndFetch2x2(const std::string& src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  LowerAndRun(design, f);
  Array2x2 out;
  out.e00 = f.ctx.FindVariable("arr[0][0]");
  out.e01 = f.ctx.FindVariable("arr[0][1]");
  out.e10 = f.ctx.FindVariable("arr[1][0]");
  out.e11 = f.ctx.FindVariable("arr[1][1]");
  EXPECT_NE(out.e00, nullptr);
  EXPECT_NE(out.e01, nullptr);
  EXPECT_NE(out.e10, nullptr);
  EXPECT_NE(out.e11, nullptr);
  return out;
}

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

TEST(ArrayLiteralSim, ConstantExpressionKeyNamesItsElement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter N = 3;\n"
      "  logic [7:0] arr [0:3];\n"
      "  initial arr = '{N-1: 8'hAA, N: 8'hBB, default: 8'h11};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x11);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x11);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xAA);
  EXPECT_EQ(f.ctx.FindVariable("arr[3]")->value.ToUint64(), 0xBB);
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

TEST(ArrayLiteralSim, MultipleIndexKeysWithDefault) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  int arr [0:2];\n"
                 "  initial begin\n"
                 "    arr = '{0: 100, 2: 200, default: 0};\n"
                 "  end\n"
                 "endmodule\n",
                 "arr", {100u, 0u, 200u});
}

TEST(ArrayLiteralSim, DescendingRangeAssignment) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  int arr [1:0];\n"
                 "  initial begin\n"
                 "    arr = '{30, 40};\n"
                 "  end\n"
                 "endmodule\n",
                 "arr", {40u, 30u});
}

TEST(ArrayLiteralSim, ReplicationMultiElement) {
  SimFixture f;
  RunModuleArray(f,
                 "module m;\n"
                 "  int arr [0:3];\n"
                 "  initial arr = '{2{5, 10}};\n"
                 "endmodule\n",
                 "arr", {5u, 10u, 5u, 10u});
}

TEST(ArrayLiteralSim, SingleElementInit) {
  SimFixture f;
  RunModuleArray(f,
                 "module m;\n"
                 "  int arr [0:0] = '{42};\n"
                 "endmodule\n",
                 "arr", {42u});
}

TEST(ArrayLiteralSim, IndexKeyOnlyAssignment) {
  SimFixture f;
  RunModuleArray(f,
                 "module m;\n"
                 "  int arr [0:2];\n"
                 "  initial arr = '{0: 10, 1: 20, 2: 30};\n"
                 "endmodule\n",
                 "arr", {10u, 20u, 30u});
}

TEST(ArrayLiteralSim, NarrowToWideContextEval) {
  SimFixture f;
  RunModuleArray(f,
                 "module m;\n"
                 "  int arr [0:1];\n"
                 "  initial arr = '{1'b1, 1'b1};\n"
                 "endmodule\n",
                 "arr", {1u, 1u});
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
  Array2x2 arr = RunAndFetch2x2(
      "module m;\n"
      "  int arr [0:1][0:1];\n"
      "  initial arr = '{'{1, 2}, '{3, 4}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(arr.e00, nullptr);
  ASSERT_NE(arr.e01, nullptr);
  ASSERT_NE(arr.e10, nullptr);
  ASSERT_NE(arr.e11, nullptr);
  EXPECT_EQ(arr.e00->value.ToUint64(), 1u);
  EXPECT_EQ(arr.e01->value.ToUint64(), 2u);
  EXPECT_EQ(arr.e10->value.ToUint64(), 3u);
  EXPECT_EQ(arr.e11->value.ToUint64(), 4u);
}

TEST(ArrayLiteralSim, DefaultMultidimensionalValues) {
  SimFixture f;
  Array2x2 arr = RunAndFetch2x2(
      "module m;\n"
      "  int arr [0:1][0:1];\n"
      "  initial arr = '{default: 42};\n"
      "endmodule\n",
      f);
  ASSERT_NE(arr.e00, nullptr);
  ASSERT_NE(arr.e01, nullptr);
  ASSERT_NE(arr.e10, nullptr);
  ASSERT_NE(arr.e11, nullptr);
  EXPECT_EQ(arr.e00->value.ToUint64(), 42u);
  EXPECT_EQ(arr.e01->value.ToUint64(), 42u);
  EXPECT_EQ(arr.e10->value.ToUint64(), 42u);
  EXPECT_EQ(arr.e11->value.ToUint64(), 42u);
}

TEST(ArrayLiteralSim, TypeKeyMatchesAllElements) {
  SimFixture f;
  RunModuleArray(f,
                 "module m;\n"
                 "  int arr [0:2] = '{int: 42, default: 0};\n"
                 "endmodule\n",
                 "arr", {42u, 42u, 42u});
}

TEST(ArrayLiteralSim, TypeKeyMismatchFallsToDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{int: 8'h05, default: 8'hFF};\n"
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
  EXPECT_EQ(e0->value.ToUint64(), 0xFFu);
  EXPECT_EQ(e1->value.ToUint64(), 0xFFu);
  EXPECT_EQ(e2->value.ToUint64(), 0xFFu);
}

TEST(ArrayLiteralSim, IndexKeyTakesPrecedenceOverTypeKey) {
  SimFixture f;
  RunModuleArray(f,
                 "module m;\n"
                 "  int arr [0:2] = '{0: 100, int: 7};\n"
                 "endmodule\n",
                 "arr", {100u, 7u, 7u});
}

TEST(ArrayLiteralSim, NestedReplicationFillsEachDimension) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int n [1:2][1:3];\n"
      "  initial n = '{2{'{3{9}}}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  for (int i = 1; i <= 2; ++i) {
    for (int j = 1; j <= 3; ++j) {
      auto name = "n[" + std::to_string(i) + "][" + std::to_string(j) + "]";
      auto* e = f.ctx.FindVariable(name);
      ASSERT_NE(e, nullptr) << name;
      EXPECT_EQ(e->value.ToUint64(), 9u) << name;
    }
  }
}

TEST(ArrayLiteralSim, IndexKeyedValueCoercedToElementWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:1];\n"
      "  initial arr = '{0: 16'h1234, 1: 16'h5678};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 0x34u);
  EXPECT_EQ(e1->value.ToUint64(), 0x78u);
}

TEST(ArrayLiteralSim, IndexKeyedValueEvaluatesExpression) {
  SimFixture f;
  RunModuleArray(f,
                 "module m;\n"
                 "  int arr [0:2];\n"
                 "  int k;\n"
                 "  initial begin\n"
                 "    k = 5;\n"
                 "    arr = '{1: k + 10, default: k};\n"
                 "  end\n"
                 "endmodule\n",
                 "arr", {5u, 15u, 5u});
}

TEST(ArrayLiteralSim, PositionalVarInitCoercesToElementWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:1] = '{16'h1234, 16'h5678};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 0x34u);
  EXPECT_EQ(e1->value.ToUint64(), 0x78u);
}

TEST(ArrayLiteralSim, KeyedVarInitCoercesToElementWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{0: 16'hAABB, default: 16'h00CC};\n"
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
  EXPECT_EQ(e0->value.ToUint64(), 0xBBu);
  EXPECT_EQ(e1->value.ToUint64(), 0xCCu);
  EXPECT_EQ(e2->value.ToUint64(), 0xCCu);
}

TEST(ArrayLiteralSim, PositionalItemVariableIsCopiedNotAliased) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } p_t;\n"
      "  p_t p;\n"
      "  p_t arr [0:1];\n"
      "  initial begin\n"
      "    p = 8'hA5;\n"
      "    arr = '{p, 8'h5A};\n"
      "    p.hi = 4'h3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* vp = f.ctx.FindVariable("p");
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(vp, nullptr);
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(vp->value.ToUint64(), 0x35u);
  EXPECT_EQ(e0->value.ToUint64(), 0xA5u);
  EXPECT_EQ(e1->value.ToUint64(), 0x5Au);
}

TEST(ArrayLiteralSim, MultidimensionalLeafVariableIsCopiedNotAliased) {
  SimFixture f;
  Array2x2 arr = RunAndFetch2x2(
      "module m;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } p_t;\n"
      "  p_t p;\n"
      "  p_t arr [0:1][0:1];\n"
      "  initial begin\n"
      "    p = 8'hC3;\n"
      "    arr = '{'{p, 8'h11}, '{8'h22, 8'h33}};\n"
      "    p.lo = 4'h7;\n"
      "  end\n"
      "endmodule\n",
      f);
  auto* vp = f.ctx.FindVariable("p");
  ASSERT_NE(vp, nullptr);
  ASSERT_NE(arr.e00, nullptr);
  ASSERT_NE(arr.e01, nullptr);
  ASSERT_NE(arr.e11, nullptr);
  EXPECT_EQ(vp->value.ToUint64(), 0xC7u);
  EXPECT_EQ(arr.e00->value.ToUint64(), 0xC3u);
  EXPECT_EQ(arr.e01->value.ToUint64(), 0x11u);
  EXPECT_EQ(arr.e11->value.ToUint64(), 0x33u);
}

TEST(ArrayLiteralSim, IndexKeyedVariableIsCopiedNotAliased) {
  SimFixture f;
  auto* e0 = RunAndFindVar(
      "module m;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } p_t;\n"
      "  p_t p;\n"
      "  p_t arr [0:1];\n"
      "  initial begin\n"
      "    p = 8'h96;\n"
      "    arr = '{0: p, default: 8'h0F};\n"
      "    p.hi = 4'h4;\n"
      "  end\n"
      "endmodule\n",
      f, "arr[0]");
  ASSERT_NE(e0, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 0x96u);
  auto* vp = f.ctx.FindVariable("p");
  ASSERT_NE(vp, nullptr);
  EXPECT_EQ(vp->value.ToUint64(), 0x46u);
  auto* e1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e1->value.ToUint64(), 0xFFu);
}

struct Array2x3 {
  Variable* e[2][3] = {};
};

Array2x3 RunAndFetch2x3(const std::string& src, SimFixture& f,
                        std::string_view name) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  LowerAndRun(design, f);
  Array2x3 out;
  for (int i = 0; i < 2; ++i) {
    for (int j = 0; j < 3; ++j) {
      auto leaf = std::string(name) + "[" + std::to_string(i + 1) + "][" +
                  std::to_string(j + 1) + "]";
      out.e[i][j] = f.ctx.FindVariable(leaf);
      EXPECT_NE(out.e[i][j], nullptr) << leaf;
    }
  }
  return out;
}

TEST(ArrayLiteralSim, NestedReplicationVarInitFillsEveryLeaf) {
  SimFixture f;
  Array2x3 n = RunAndFetch2x3(
      "module m;\n"
      "  parameter int y = 7;\n"
      "  int n [1:2][1:3] = '{2{'{3{y}}}};\n"
      "endmodule\n",
      f, "n");
  for (int i = 0; i < 2; ++i) {
    for (int j = 0; j < 3; ++j) {
      ASSERT_NE(n.e[i][j], nullptr) << i << " " << j;
      EXPECT_EQ(n.e[i][j]->value.ToUint64(), 7u) << i << " " << j;
    }
  }
}

TEST(ArrayLiteralSim, PositionalNestedVarInitIsRowMajor) {
  SimFixture f;
  Array2x3 g = RunAndFetch2x3(
      "module m;\n"
      "  bit [7:0] g [1:2][1:3] = '{'{8'h11, 8'h22, 8'h33},\n"
      "                             '{8'h44, 8'h55, 8'h66}};\n"
      "endmodule\n",
      f, "g");
  ASSERT_NE(g.e[0][0], nullptr);
  ASSERT_NE(g.e[0][1], nullptr);
  ASSERT_NE(g.e[0][2], nullptr);
  ASSERT_NE(g.e[1][0], nullptr);
  ASSERT_NE(g.e[1][1], nullptr);
  ASSERT_NE(g.e[1][2], nullptr);
  EXPECT_EQ(g.e[0][0]->value.ToUint64(), 0x11u);
  EXPECT_EQ(g.e[0][1]->value.ToUint64(), 0x22u);
  EXPECT_EQ(g.e[0][2]->value.ToUint64(), 0x33u);
  EXPECT_EQ(g.e[1][0]->value.ToUint64(), 0x44u);
  EXPECT_EQ(g.e[1][1]->value.ToUint64(), 0x55u);
  EXPECT_EQ(g.e[1][2]->value.ToUint64(), 0x66u);
}

TEST(ArrayLiteralSim, VarInitLeafMatchesProceduralAssignLeaf) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int d [1:2][1:3] = '{'{10, 20, 30}, '{40, 50, 60}};\n"
      "  int p [1:2][1:3];\n"
      "  initial p = '{'{10, 20, 30}, '{40, 50, 60}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  for (uint64_t i = 1; i <= 2; ++i) {
    for (uint64_t j = 1; j <= 3; ++j) {
      auto suffix = "[" + std::to_string(i) + "][" + std::to_string(j) + "]";
      auto* declared = f.ctx.FindVariable("d" + suffix);
      auto* assigned = f.ctx.FindVariable("p" + suffix);
      ASSERT_NE(declared, nullptr) << suffix;
      ASSERT_NE(assigned, nullptr) << suffix;
      uint64_t want = ((i - 1) * 3 + j) * 10;
      EXPECT_EQ(assigned->value.ToUint64(), want) << suffix;
      EXPECT_EQ(declared->value.ToUint64(), want) << suffix;
    }
  }
}

TEST(ArrayLiteralSim, DescendingOuterDimVarInitAndAssignAgree) {
  SimFixture f;
  Array2x3 a = RunAndFetch2x3(
      "module m;\n"
      "  int a [2:1][1:3] = '{'{1, 2, 3}, '{4, 5, 6}};\n"
      "  int b [2:1][1:3];\n"
      "  initial b = '{'{1, 2, 3}, '{4, 5, 6}};\n"
      "endmodule\n",
      f, "a");
  const uint64_t kRows[2][3] = {{4u, 5u, 6u}, {1u, 2u, 3u}};
  for (int i = 0; i < 2; ++i) {
    for (int j = 0; j < 3; ++j) {
      std::string leaf =
          "b[" + std::to_string(i + 1) + "][" + std::to_string(j + 1) + "]";
      auto* proc = f.ctx.FindVariable(leaf);
      ASSERT_NE(a.e[i][j], nullptr) << leaf;
      ASSERT_NE(proc, nullptr) << leaf;
      EXPECT_EQ(a.e[i][j]->value.ToUint64(), kRows[i][j]) << leaf;
      EXPECT_EQ(proc->value.ToUint64(), kRows[i][j]) << leaf;
      EXPECT_EQ(proc->value.ToUint64(), a.e[i][j]->value.ToUint64()) << leaf;
    }
  }
}

TEST(ArrayLiteralSim, DescendingInnerDimTakesItemsFromLeftBound) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int c [2:1][1:3];\n"
      "  int d [1:2][3:1];\n"
      "  initial begin\n"
      "    c = '{'{10, 20, 30}, '{40, 50, 60}};\n"
      "    d = '{'{10, 20, 30}, '{40, 50, 60}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  const uint64_t kOuterDesc[2][3] = {{40u, 50u, 60u}, {10u, 20u, 30u}};
  const uint64_t kInnerDesc[2][3] = {{30u, 20u, 10u}, {60u, 50u, 40u}};
  for (int i = 0; i < 2; ++i) {
    for (int j = 0; j < 3; ++j) {
      std::string addr =
          "[" + std::to_string(i + 1) + "][" + std::to_string(j + 1) + "]";
      auto* outer = f.ctx.FindVariable("c" + addr);
      auto* inner = f.ctx.FindVariable("d" + addr);
      ASSERT_NE(outer, nullptr) << addr;
      ASSERT_NE(inner, nullptr) << addr;
      EXPECT_EQ(outer->value.ToUint64(), kOuterDesc[i][j]) << addr;
      EXPECT_EQ(inner->value.ToUint64(), kInnerDesc[i][j]) << addr;
    }
  }
}

TEST(ArrayLiteralSim, AscendingDimsUnchangedByPerDimensionDirection) {
  SimFixture f;
  Array2x3 e = RunAndFetch2x3(
      "module m;\n"
      "  int e [1:2][1:3] = '{'{1, 2, 3}, '{4, 5, 6}};\n"
      "  int p [1:2][1:3];\n"
      "  initial p = '{'{1, 2, 3}, '{4, 5, 6}};\n"
      "endmodule\n",
      f, "e");
  for (uint64_t i = 0; i < 2; ++i) {
    for (uint64_t j = 0; j < 3; ++j) {
      uint64_t want = i * 3 + j + 1;
      std::string cell =
          "p[" + std::to_string(i + 1) + "][" + std::to_string(j + 1) + "]";
      auto* assigned = f.ctx.FindVariable(cell);
      ASSERT_NE(e.e[i][j], nullptr) << cell;
      ASSERT_NE(assigned, nullptr) << cell;
      EXPECT_EQ(e.e[i][j]->value.ToUint64(), want) << cell;
      EXPECT_EQ(assigned->value.ToUint64(), want) << cell;
    }
  }
}

TEST(ArrayLiteralSim, TypeKeyReachesEveryLeafOfMultidimAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int d [1:2][1:3] = '{int: 7};\n"
      "  int p [1:2][1:3];\n"
      "  initial p = '{int: 7};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  const std::string kLeaves[6] = {"[1][1]", "[1][2]", "[1][3]",
                                  "[2][1]", "[2][2]", "[2][3]"};
  for (const auto& leaf : kLeaves) {
    auto* declared = f.ctx.FindVariable("d" + leaf);
    auto* assigned = f.ctx.FindVariable("p" + leaf);
    ASSERT_NE(declared, nullptr) << leaf;
    ASSERT_NE(assigned, nullptr) << leaf;
    EXPECT_EQ(declared->value.ToUint64(), 7u) << leaf;
    EXPECT_EQ(assigned->value.ToUint64(), 7u) << leaf;
  }
}

TEST(ArrayLiteralSim, MultidimKeyOrderIsIndexThenTypeThenDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [1:2][1:3];\n"
      "  initial q = '{1: 100, int: 7, default: 55};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  const uint64_t kRowValue[2] = {100u, 7u};
  for (uint32_t i = 1; i <= 2; ++i) {
    for (uint32_t j = 1; j <= 3; ++j) {
      std::string leaf =
          "q[" + std::to_string(i) + "][" + std::to_string(j) + "]";
      auto* e = f.ctx.FindVariable(leaf);
      ASSERT_NE(e, nullptr) << leaf;
      EXPECT_EQ(e->value.ToUint64(), kRowValue[i - 1]) << leaf;
    }
  }
}

}  // namespace
