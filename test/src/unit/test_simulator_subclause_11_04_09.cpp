#include <gtest/gtest.h>

#include <cstdint>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "lexer/token.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

uint64_t EvalReduceToU64(SimFixture& f, TokenKind op) {
  auto* expr = MakeUnary(f.arena, op, MakeId(f.arena, "v"));
  return EvalExpr(expr, f.ctx, f.arena).ToUint64();
}

uint64_t EvalReduceBval(SimFixture& f, TokenKind op) {
  auto* expr = MakeUnary(f.arena, op, MakeId(f.arena, "v"));
  return EvalExpr(expr, f.ctx, f.arena).words[0].bval;
}

TEST(EvalOpXZ, ReductionAndWithX) {
  SimFixture f;

  MakeVar4(f, "ra", 4, 0b1011, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeId(f.arena, "ra"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionAndWithKnown0) {
  SimFixture f;

  MakeVar4(f, "rb", 4, 0b0011, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeId(f.arena, "rb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionOrWithKnown1) {
  SimFixture f;

  MakeVar4(f, "rc", 4, 0b1000, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeId(f.arena, "rc"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionOrWithX) {
  SimFixture f;

  MakeVar4(f, "rd", 4, 0b0000, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeId(f.arena, "rd"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionXorWithX) {
  SimFixture f;

  MakeVar4(f, "re", 4, 0b1010, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kCaret, MakeId(f.arena, "re"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(OperatorSim, UnaryReductionAnd) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = &8'hFF;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, UnaryReductionNand) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = ~&8'hFF;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(OperatorSim, UnaryReductionOr) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = |8'h00;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(OperatorSim, UnaryReductionNor) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = ~|8'h00;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, UnaryReductionXor) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = ^8'hA5;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(OperatorSim, UnaryReductionXnor) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = ~^8'hA5;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, UnaryReductionXnorAlt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = ^~8'hA5;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(EvalOpXZ, ReductionAndWithZKnown0) {
  SimFixture f;

  MakeVar4(f, "v", 4, 0b0110, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionAndWithZNoKnown0) {
  SimFixture f;

  MakeVar4(f, "v", 4, 0b1111, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionOrWithZKnown1) {
  SimFixture f;

  MakeVar4(f, "v", 4, 0b1100, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionOrWithZNoKnown1) {
  SimFixture f;

  MakeVar4(f, "v", 4, 0b0100, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionXorWithZ) {
  SimFixture f;

  MakeVar4(f, "v", 4, 0b1110, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kCaret, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionNandWithXNoKnown0) {
  SimFixture f;

  MakeVar4(f, "v", 4, 0b1011, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kTildeAmp, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionNandWithXKnown0) {
  SimFixture f;

  MakeVar4(f, "v", 4, 0b0011, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kTildeAmp, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionNorWithXKnown1) {
  SimFixture f;

  MakeVar4(f, "v", 4, 0b1000, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kTildePipe, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionNorWithXNoKnown1) {
  SimFixture f;

  MakeVar4(f, "v", 4, 0b0000, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kTildePipe, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionXnorWithX) {
  SimFixture f;

  MakeVar4(f, "v", 4, 0b1010, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kTildeCaret, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionNandWithZ) {
  SimFixture f;

  MakeVar4(f, "v", 4, 0b1111, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kTildeAmp, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionNorWithZ) {
  SimFixture f;

  MakeVar4(f, "v", 4, 0b0100, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kTildePipe, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ReductionXnorWithZ) {
  SimFixture f;

  MakeVar4(f, "v", 4, 0b1110, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kTildeCaret, MakeId(f.arena, "v"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOp, ReductionAndResultIsOneBit) {
  SimFixture f;
  auto* expr =
      MakeUnary(f.arena, TokenKind::kAmp, MakeInt(f.arena, 0xFFFFFFFF));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(EvalOp, ReductionOrResultIsOneBit) {
  SimFixture f;
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(EvalOp, ReductionXorResultIsOneBit) {
  SimFixture f;
  auto* expr = MakeUnary(f.arena, TokenKind::kCaret, MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(EvalOp, ReductionNandResultIsOneBit) {
  SimFixture f;
  auto* expr = MakeUnary(f.arena, TokenKind::kTildeAmp, MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(EvalOp, ReductionNorResultIsOneBit) {
  SimFixture f;
  auto* expr = MakeUnary(f.arena, TokenKind::kTildePipe, MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(EvalOp, ReductionXnorResultIsOneBit) {
  SimFixture f;
  auto* expr = MakeUnary(f.arena, TokenKind::kTildeCaret, MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(EvalOp, AllReductionsOnAllZeros) {
  SimFixture f;

  MakeVar4(f, "v", 4, 0b0000, 0);

  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kAmp), 0u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kTildeAmp), 1u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kPipe), 0u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kTildePipe), 1u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kCaret), 0u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kTildeCaret), 1u);
}

TEST(EvalOp, AllReductionsOnAllOnes) {
  SimFixture f;

  MakeVar4(f, "v", 4, 0b1111, 0);

  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kAmp), 1u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kTildeAmp), 0u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kPipe), 1u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kTildePipe), 0u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kCaret), 0u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kTildeCaret), 1u);
}

TEST(EvalOp, AllReductionsOnEvenOnes) {
  SimFixture f;

  MakeVar4(f, "v", 4, 0b0110, 0);

  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kAmp), 0u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kTildeAmp), 1u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kPipe), 1u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kTildePipe), 0u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kCaret), 0u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kTildeCaret), 1u);
}

TEST(EvalOp, AllReductionsOnOddOnes) {
  SimFixture f;

  MakeVar4(f, "v", 4, 0b1000, 0);

  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kAmp), 0u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kTildeAmp), 1u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kPipe), 1u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kTildePipe), 0u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kCaret), 1u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kTildeCaret), 0u);
}

TEST(EvalOpXZ, AllReductionsOnAllX) {
  SimFixture f;
  MakeVar4(f, "v", 4, 0b0000, 0b1111);

  EXPECT_NE(EvalReduceBval(f, TokenKind::kAmp), 0u);
  EXPECT_NE(EvalReduceBval(f, TokenKind::kPipe), 0u);
  EXPECT_NE(EvalReduceBval(f, TokenKind::kCaret), 0u);
  EXPECT_NE(EvalReduceBval(f, TokenKind::kTildeAmp), 0u);
  EXPECT_NE(EvalReduceBval(f, TokenKind::kTildePipe), 0u);
  EXPECT_NE(EvalReduceBval(f, TokenKind::kTildeCaret), 0u);
}

TEST(EvalOpXZ, AllReductionsOnAllZ) {
  SimFixture f;
  MakeVar4(f, "v", 4, 0b1111, 0b1111);

  EXPECT_NE(EvalReduceBval(f, TokenKind::kAmp), 0u);
  EXPECT_NE(EvalReduceBval(f, TokenKind::kPipe), 0u);
  EXPECT_NE(EvalReduceBval(f, TokenKind::kCaret), 0u);
  EXPECT_NE(EvalReduceBval(f, TokenKind::kTildeAmp), 0u);
  EXPECT_NE(EvalReduceBval(f, TokenKind::kTildePipe), 0u);
  EXPECT_NE(EvalReduceBval(f, TokenKind::kTildeCaret), 0u);
}

TEST(EvalOp, ReductionFirstStepWidthTwo) {
  SimFixture f;
  MakeVar4(f, "v", 2, 0b10, 0);

  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kAmp), 0u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kPipe), 1u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kCaret), 1u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kTildeAmp), 1u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kTildePipe), 0u);
  EXPECT_EQ(EvalReduceToU64(f, TokenKind::kTildeCaret), 0u);
}

TEST(OperatorSim, ReductionAndXOperandFullPipeline) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    v = 4'b111x;\n"
      "    r = &v;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_FALSE(r->value.IsKnown());
}

TEST(OperatorSim, ReductionOrKnownOneAbsorbsXFullPipeline) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    v = 4'b100x;\n"
      "    r = |v;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_TRUE(r->value.IsKnown());
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

TEST(OperatorSim, ReductionXorXOperandFullPipeline) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    v = 4'b10x0;\n"
      "    r = ^v;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_FALSE(r->value.IsKnown());
}

TEST(OperatorSim, ReductionNandXOperandStaysXFullPipeline) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    v = 4'b111x;\n"
      "    r = ~&v;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_FALSE(r->value.IsKnown());
}

TEST(OperatorSim, ReductionOrZOperandFullPipeline) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    v = 4'bzzzz;\n"
      "    r = |v;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_FALSE(r->value.IsKnown());
}

TEST(OperatorSim, ReductionOverWideMultiWordOperand) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [99:0] v;\n"
      "  logic r_and;\n"
      "  logic r_xor;\n"
      "  initial begin\n"
      "    v = '1;\n"
      "    r_and = &v;\n"
      "    r_xor = ^v;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* r_and = f.ctx.FindVariable("r_and");
  auto* r_xor = f.ctx.FindVariable("r_xor");
  ASSERT_NE(r_and, nullptr);
  ASSERT_NE(r_xor, nullptr);
  EXPECT_EQ(r_and->value.ToUint64(), 1u);
  EXPECT_EQ(r_xor->value.ToUint64(), 0u);
}

TEST(OperatorSim, ReductionOverTwoStateOperand) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [3:0] v;\n"
      "  logic r_and;\n"
      "  logic r_xor;\n"
      "  initial begin\n"
      "    v = 4'b1011;\n"
      "    r_and = &v;\n"
      "    r_xor = ^v;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* r_and = f.ctx.FindVariable("r_and");
  auto* r_xor = f.ctx.FindVariable("r_xor");
  ASSERT_NE(r_and, nullptr);
  ASSERT_NE(r_xor, nullptr);
  EXPECT_TRUE(r_and->value.IsKnown());
  EXPECT_EQ(r_and->value.ToUint64(), 0u);
  EXPECT_TRUE(r_xor->value.IsKnown());
  EXPECT_EQ(r_xor->value.ToUint64(), 1u);
}

TEST(OperatorSim, ReductionOverSingleBitOperand) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic v;\n"
      "  logic r_and;\n"
      "  logic r_or;\n"
      "  logic r_xor;\n"
      "  initial begin\n"
      "    v = 1'b1;\n"
      "    r_and = &v;\n"
      "    r_or = |v;\n"
      "    r_xor = ^v;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("r_and")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("r_or")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("r_xor")->value.ToUint64(), 1u);
}

TEST(OperatorSim, ReductionInContinuousAssign) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  logic y;\n"
      "  assign y = &a;\n"
      "  initial a = 4'b1111;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

TEST(OperatorSim, ReductionOverParameterOperand) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  parameter [3:0] P = 4'b1110;\n"
      "  logic r;\n"
      "  initial r = ^P;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

}  // namespace
