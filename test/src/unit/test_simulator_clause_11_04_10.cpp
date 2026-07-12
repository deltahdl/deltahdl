#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(EvalOpXZ, ShiftXAmount) {
  SimFixture f;

  MakeVar4(f, "sa", 4, 0b0000, 0b0100);
  auto* a = f.ctx.CreateVariable("sv", 4);
  a->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtLt, MakeId(f.arena, "sv"),
                          MakeId(f.arena, "sa"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ShiftLeftXOperand) {
  SimFixture f;

  MakeVar4(f, "so", 4, 0b1000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtLt, MakeId(f.arena, "so"),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.words[0].aval & 0xFu, 0b0000u);
  EXPECT_EQ(result.words[0].bval & 0xFu, 0b1000u);
}

TEST(ExpressionSim, LeftShift) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd1 << 3;\n"
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

TEST(ExpressionSim, RightShift) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd16 >> 2;\n"
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

TEST(OperatorSim, BinaryArithLeftShift) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd3 <<< 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(OperatorSim, BinaryArithRightShift) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd64 >>> 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(OperatorSim, ArithRightShiftUnsignedZeroFills) {
  SimFixture f;

  MakeVar(f, "u", 4, 0b1000);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtGtGt, MakeId(f.arena, "u"),
                          MakeInt(f.arena, 2));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64() & 0xFu, 0b0010u);
}

TEST(EvalOpXZ, ArithRightShiftXAmount) {
  SimFixture f;
  MakeVar(f, "v", 4, 0b1100);
  MakeVar4(f, "sa", 4, 0b0000, 0b0010);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtGtGt, MakeId(f.arena, "v"),
                          MakeId(f.arena, "sa"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalRightShiftXAmount) {
  SimFixture f;
  MakeVar(f, "v", 4, 0b1100);
  MakeVar4(f, "sa", 4, 0b0000, 0b0010);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtGt, MakeId(f.arena, "v"),
                          MakeId(f.arena, "sa"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// §11.4.10: an x or z in the shift amount makes the result unknown. This holds
// for every shift operator, so the arithmetic left shift completes the set
// already exercised for <<, >>, and >>>.
TEST(EvalOpXZ, ArithLeftShiftXAmount) {
  SimFixture f;
  MakeVar(f, "v", 4, 0b1100);
  MakeVar4(f, "sa", 4, 0b0000, 0b0010);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtLtLt, MakeId(f.arena, "v"),
                          MakeId(f.arena, "sa"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalRightShiftXOperand) {
  SimFixture f;

  MakeVar4(f, "so", 4, 0b1000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtGt, MakeId(f.arena, "so"),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.words[0].aval & 0xFu, 0b0100u);
  EXPECT_EQ(result.words[0].bval & 0xFu, 0b0010u);
}

TEST(OperatorSim, ShiftResultSignednessFromLhs) {
  SimFixture f;

  MakeSignedVarAdv(f, "s", 8, 0x0F);
  MakeVar(f, "amt", 4, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtLt, MakeId(f.arena, "s"),
                          MakeId(f.arena, "amt"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);

  MakeVar(f, "u", 8, 0x0F);
  MakeSignedVarAdv(f, "samt", 4, 2);
  auto* expr2 = MakeBinary(f.arena, TokenKind::kLtLt, MakeId(f.arena, "u"),
                           MakeId(f.arena, "samt"));
  auto result2 = EvalExpr(expr2, f.ctx, f.arena);
  EXPECT_FALSE(result2.is_signed);
}

TEST(OperatorSim, AllShiftOpsPreserveLhsSignedness) {
  SimFixture f;
  MakeSignedVarAdv(f, "s", 8, 0x0F);
  MakeVar(f, "amt", 4, 1);

  TokenKind ops[] = {TokenKind::kLtLt, TokenKind::kGtGt, TokenKind::kLtLtLt,
                     TokenKind::kGtGtGt};
  for (auto op : ops) {
    auto* expr =
        MakeBinary(f.arena, op, MakeId(f.arena, "s"), MakeId(f.arena, "amt"));
    auto result = EvalExpr(expr, f.ctx, f.arena);
    EXPECT_TRUE(result.is_signed);
  }
}

// §11.4.10: the shift amount is always treated as an unsigned number. A signed
// right operand whose sign bit is set is applied as its (large) unsigned
// magnitude, never as a negative count. The 5-bit signed amount 0b10000 here is
// 16 when read unsigned, shifting the 32-bit all-ones operand down to its upper
// half rather than doing anything sign-driven.
TEST(OperatorSim, ShiftAmountTreatedAsUnsigned) {
  SimFixture f;
  MakeVar(f, "u", 32, 0xFFFFFFFFu);
  MakeSignedVarAdv(f, "amt", 5, 0b10000);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtGt, MakeId(f.arena, "u"),
                          MakeId(f.arena, "amt"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFFFFFFFFull, 0xFFFFu);
}

TEST(OperatorSim, ShiftByZero) {
  SimFixture f;
  MakeVar(f, "v", 8, 0xAB);
  TokenKind ops[] = {TokenKind::kLtLt, TokenKind::kGtGt, TokenKind::kLtLtLt,
                     TokenKind::kGtGtGt};
  for (auto op : ops) {
    auto* expr =
        MakeBinary(f.arena, op, MakeId(f.arena, "v"), MakeInt(f.arena, 0));
    auto result = EvalExpr(expr, f.ctx, f.arena);
    EXPECT_EQ(result.ToUint64() & 0xFFu, 0xABu);
  }
}

TEST(OperatorSim, ShiftByMoreThanWidth) {
  SimFixture f;
  MakeVar(f, "v", 4, 0b1111);
  auto* expr_l = MakeBinary(f.arena, TokenKind::kLtLt, MakeId(f.arena, "v"),
                            MakeInt(f.arena, 5));
  EXPECT_EQ(EvalExpr(expr_l, f.ctx, f.arena).ToUint64() & 0xFu, 0u);

  auto* expr_r = MakeBinary(f.arena, TokenKind::kGtGt, MakeId(f.arena, "v"),
                            MakeInt(f.arena, 5));
  EXPECT_EQ(EvalExpr(expr_r, f.ctx, f.arena).ToUint64() & 0xFu, 0u);
}

// §11.4.10: the arithmetic right shift sign-fills the vacated high bits when
// the result type is signed. Signedness is a property of the operand's
// declaration, so this drives a real `logic signed` variable through the full
// pipeline: the lowerer propagates the declared signedness onto the runtime
// value and the runtime shift reads it to choose sign-fill over zero-fill.
// 4'b1000 is -8, and an arithmetic right shift by 1 yields 4'b1100 (-4) rather
// than the 4'b0100 a zero-fill would produce, so the fill source is observed
// from source syntax.
TEST(OperatorSim, ArithRightShiftSignedDeclSignFillsFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [3:0] s;\n"
      "  logic signed [3:0] r;\n"
      "  initial begin\n"
      "    s = 4'b1000;\n"
      "    r = s >>> 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64() & 0xFu, 0b1100u);
}

// §11.4.10: an x or z in the shift amount forces an unknown result. The
// synthetic EvalOpXZ cases above hand-build a z amount (aval=0, bval=1); this
// drives a true-x amount (the 4'bx literal lowers to aval=1, bval=1) through
// the full pipeline from real source, so the HasUnknownBits gate is observed
// acting on an amount produced exactly the way a design would produce one.
TEST(OperatorSim, UnknownShiftAmountFromSourceYieldsUnknown) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  logic [3:0] amt;\n"
      "  initial begin\n"
      "    amt = 4'bx;\n"
      "    r = 8'hFF >> amt;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_NE(r->value.words[0].bval & 0xFFu, 0u);
}

TEST(AlwaysCombBasicSim, AlwaysCombBitSelect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'b0000_0100;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a >> 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(AlwaysCombBasicSim, AlwaysCombUpperPartSelect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = (a >> 4) & 8'h0F;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

TEST(AlwaysCombBasicSim, AlwaysCombShift) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, result;\n"
      "  initial a = 8'b0000_0011;\n"
      "  always_comb begin\n"
      "    result = a << 4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x30u);
}

TEST(BlockingAssignSim, BlockingAssignShiftOps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] r_shl, r_shr;\n"
      "  initial begin\n"
      "    a = 8'h0F;\n"
      "    r_shl = a << 2;\n"
      "    r_shr = a >> 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* shl = f.ctx.FindVariable("r_shl");
  auto* shr = f.ctx.FindVariable("r_shr");
  ASSERT_NE(shl, nullptr);
  ASSERT_NE(shr, nullptr);

  EXPECT_EQ(shl->value.ToUint64(), 0x3Cu);

  EXPECT_EQ(shr->value.ToUint64(), 0x03u);
}

}  // namespace
