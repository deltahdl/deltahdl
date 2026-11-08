#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SubroutineCallExprSim, SystemTfCallClog2) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = $clog2(256);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

TEST(UtilitySystemTaskTest, Clog2ZeroAndOneFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int z;\n"
      "  int one;\n"
      "  int xz;\n"
      "  int x1;\n"
      "  initial begin\n"
      "    z = 0;\n"
      "    one = 1;\n"
      "    xz = $clog2(z);\n"
      "    x1 = $clog2(one);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* xz = f.ctx.FindVariable("xz");
  auto* x1 = f.ctx.FindVariable("x1");
  ASSERT_NE(xz, nullptr);
  ASSERT_NE(x1, nullptr);
  EXPECT_EQ(xz->value.ToUint64(), 0u);
  EXPECT_EQ(x1->value.ToUint64(), 0u);
}

TEST(UtilitySystemTaskTest, Clog2TreatsArgumentAsUnsigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int neg;\n"
      "  int x;\n"
      "  initial begin\n"
      "    neg = -2;\n"
      "    x = $clog2(neg);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 32u);
}

TEST(UtilitySystemTaskTest, Clog2VectorArgument) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] depth;\n"
      "  int x;\n"
      "  initial begin\n"
      "    depth = 16'd300;\n"
      "    x = $clog2(depth);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

TEST(UtilitySystemTaskTest, Clog2WideVectorArgument) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [39:0] big;\n"
      "  int x;\n"
      "  initial begin\n"
      "    big = 40'd8589934593;\n"
      "    x = $clog2(big);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 34u);
}

}  // namespace
