#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SubroutineCallExprSim, SystemTfCallClog2) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = $clog2(256);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

TEST(PrimarySim, PrimarySystemCallClog2) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial x = $clog2(16);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

// Claim D: an argument of 0 produces 0; claim A boundary at 1 produces 0.
TEST(UtilitySystemTaskTest, Clog2Zero) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$clog2", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(UtilitySystemTaskTest, Clog2One) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$clog2", {MakeInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// Claim A: ceiling of log base 2 for both powers of two and non-powers.
TEST(UtilitySystemTaskTest, Clog2Two) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$clog2", {MakeInt(f.arena, 2)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(UtilitySystemTaskTest, Clog2Three) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$clog2", {MakeInt(f.arena, 3)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
}

TEST(UtilitySystemTaskTest, Clog2PowerOf2) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$clog2", {MakeInt(f.arena, 256)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 8u);
}

TEST(UtilitySystemTaskTest, Clog2NonPowerOf2) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$clog2", {MakeInt(f.arena, 257)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 9u);
}

// Claim C: the argument is treated as unsigned. A negative 32-bit value is
// read over its unsigned bit pattern (-2 is 0xFFFFFFFE), so the result is the
// clog2 of that large magnitude rather than 0.
TEST(UtilitySystemTaskTest, Clog2TreatsArgumentAsUnsigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int neg;\n"
      "  int x;\n"
      "  initial begin\n"
      "    neg = -2;\n"
      "    x = $clog2(neg);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 32u);
}

// Claim B: the argument may be an arbitrary-sized vector value.
TEST(UtilitySystemTaskTest, Clog2VectorArgument) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] depth;\n"
      "  int x;\n"
      "  initial begin\n"
      "    depth = 16'd300;\n"
      "    x = $clog2(depth);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

// Claim B edge case: the argument may be a vector wider than the native
// machine integer. 0x2_0000_0001 (2**33 + 1) sits just past a power of two,
// so the unsigned, wide-operand result rounds up to 34.
TEST(UtilitySystemTaskTest, Clog2WideVectorArgument) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [39:0] big;\n"
      "  int x;\n"
      "  initial begin\n"
      "    big = 40'd8589934593;\n"
      "    x = $clog2(big);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 34u);
}

}  // namespace
