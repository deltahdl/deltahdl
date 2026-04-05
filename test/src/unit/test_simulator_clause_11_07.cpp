#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(SignedExprSim, SystemTfCallUnsigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = $unsigned(8'sd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(SignedExprSim, UnsignedPreservesValue) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$unsigned", {MakeInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(SignedExprSim, SignedPreservesValue) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$signed", {MakeInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(SignedExprSim, SignedSetsSignedFlag) {
  SimFixture f;
  MakeVar(f, "a", 8, 0xAB);
  auto* expr = MakeSysCall(f.arena, "$signed", {MakeId(f.arena, "a")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
  EXPECT_EQ(result.ToUint64(), 0xABu);
  EXPECT_EQ(result.width, 8u);
}

TEST(SignedExprSim, UnsignedClearsSignedFlag) {
  SimFixture f;
  MakeSignedVarAdv(f, "a", 8, 0xAB);
  auto* expr = MakeSysCall(f.arena, "$unsigned", {MakeId(f.arena, "a")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
  EXPECT_EQ(result.ToUint64(), 0xABu);
  EXPECT_EQ(result.width, 8u);
}

TEST(SignedExprSim, SignedPreservesWidth) {
  SimFixture f;
  MakeVar(f, "w", 16, 0x1234);
  auto* expr = MakeSysCall(f.arena, "$signed", {MakeId(f.arena, "w")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0x1234u);
}

TEST(SignedExprSim, UnsignedPreservesWidth) {
  SimFixture f;
  MakeSignedVarAdv(f, "w", 16, 0x1234);
  auto* expr = MakeSysCall(f.arena, "$unsigned", {MakeId(f.arena, "w")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0x1234u);
}

TEST(SignedExprSim, SignedOnAlreadySignedIsNoop) {
  SimFixture f;
  MakeSignedVarAdv(f, "s", 8, 0xFF);
  auto* expr = MakeSysCall(f.arena, "$signed", {MakeId(f.arena, "s")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
  EXPECT_EQ(result.width, 8u);
}

TEST(SignedExprSim, UnsignedOnAlreadyUnsignedIsNoop) {
  SimFixture f;
  MakeVar(f, "u", 8, 0xFF);
  auto* expr = MakeSysCall(f.arena, "$unsigned", {MakeId(f.arena, "u")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
  EXPECT_EQ(result.width, 8u);
}

TEST(SignedExprSim, SignedPreservesBitPattern) {
  SimFixture f;
  MakeVar(f, "v", 8, 0b11001010);
  auto* expr = MakeSysCall(f.arena, "$signed", {MakeId(f.arena, "v")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0b11001010u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(SignedExprSim, UnsignedPreservesBitPattern) {
  SimFixture f;
  MakeSignedVarAdv(f, "v", 8, 0b11001010);
  auto* expr = MakeSysCall(f.arena, "$unsigned", {MakeId(f.arena, "v")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0b11001010u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(SignedExprSim, EmptyArgsReturnsZero) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$signed", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SignedExprSim, LrmExampleUnsignedNeg4) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] regA;\n"
      "  initial regA = $unsigned(-4);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("regA");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

TEST(SignedExprSim, LrmExampleSignedBitLiteral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [7:0] regS;\n"
      "  initial regS = $signed(4'b1100);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("regS");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

TEST(SignedExprSim, SignedAdditionEndToEnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] regA, regB;\n"
      "  logic signed [7:0] regS;\n"
      "  initial begin\n"
      "    regA = 8'hFF;\n"
      "    regB = 8'h01;\n"
      "    regS = $signed(regA) + $signed(regB);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("regS");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(SignedExprSim, SystemTfCallSigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [7:0] x;\n"
      "  initial x = $signed(8'd200);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 200u);
}

}  // namespace
