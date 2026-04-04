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

TEST(OperatorSim, BinaryLogicalLeftShift) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd1 << 4;\n"
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

TEST(OperatorSim, BinaryLogicalRightShift) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd128 >> 3;\n"
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

// §11.4.10: Arithmetic right shift fills with sign bit when result type is
// signed (LRM Example 2: signed 4'b1000 >>> 2 yields 4'b1110).
TEST(OperatorSim, ArithRightShiftSignedSignExtends) {
  SimFixture f;
  // Signed variable with MSB set: 4'b1000 = -8 signed.
  MakeSignedVarAdv(f, "s", 4, 0b1000);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtGtGt, MakeId(f.arena, "s"),
                          MakeInt(f.arena, 2));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // Vacated bits filled with sign bit (1), so 4'b1110 = 14 unsigned / -2.
  EXPECT_EQ(result.ToUint64() & 0xFu, 0b1110u);
}

// §11.4.10: Arithmetic right shift fills with zeros when result type is
// unsigned, even if the MSB is 1.
TEST(OperatorSim, ArithRightShiftUnsignedZeroFills) {
  SimFixture f;
  // Unsigned variable with MSB set: 4'b1000 = 8 unsigned.
  MakeVar(f, "u", 4, 0b1000);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtGtGt, MakeId(f.arena, "u"),
                          MakeInt(f.arena, 2));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // Unsigned: vacated bits filled with 0, so 4'b0010 = 2.
  EXPECT_EQ(result.ToUint64() & 0xFu, 0b0010u);
}

// §11.4.10: If the right operand has an x or z value, the result is unknown.
TEST(EvalOpXZ, ArithRightShiftXAmount) {
  SimFixture f;
  MakeVar(f, "v", 4, 0b1100);
  MakeVar4(f, "sa", 4, 0b0000, 0b0010);  // x in shift amount
  auto* expr = MakeBinary(f.arena, TokenKind::kGtGtGt, MakeId(f.arena, "v"),
                          MakeId(f.arena, "sa"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// §11.4.10: If the right operand has an x or z value, the result is unknown
// (logical right shift variant).
TEST(EvalOpXZ, LogicalRightShiftXAmount) {
  SimFixture f;
  MakeVar(f, "v", 4, 0b1100);
  MakeVar4(f, "sa", 4, 0b0000, 0b0010);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtGt, MakeId(f.arena, "v"),
                          MakeId(f.arena, "sa"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// §11.4.10: X/Z bits in the LHS propagate through logical right shift.
TEST(EvalOpXZ, LogicalRightShiftXOperand) {
  SimFixture f;
  // aval=0b1000, bval=0b0100 → bit2 is x, bit3 is 1.
  MakeVar4(f, "so", 4, 0b1000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtGt, MakeId(f.arena, "so"),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // After >> 1: bit1 is x (was bit2), bit2 is 1 (was bit3).
  EXPECT_EQ(result.words[0].aval & 0xFu, 0b0100u);
  EXPECT_EQ(result.words[0].bval & 0xFu, 0b0010u);
}

// §11.4.10: The right operand is always treated as unsigned and has no effect
// on the signedness of the result.
TEST(OperatorSim, ShiftResultSignednessFromLhs) {
  SimFixture f;
  // Signed LHS, unsigned RHS.
  MakeSignedVarAdv(f, "s", 8, 0x0F);
  MakeVar(f, "amt", 4, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtLt, MakeId(f.arena, "s"),
                          MakeId(f.arena, "amt"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);

  // Unsigned LHS, signed RHS — result still unsigned.
  MakeVar(f, "u", 8, 0x0F);
  MakeSignedVarAdv(f, "samt", 4, 2);
  auto* expr2 = MakeBinary(f.arena, TokenKind::kLtLt, MakeId(f.arena, "u"),
                           MakeId(f.arena, "samt"));
  auto result2 = EvalExpr(expr2, f.ctx, f.arena);
  EXPECT_FALSE(result2.is_signed);
}

// §11.4.10: Result signedness is preserved from LHS for all four shift
// operators.
TEST(OperatorSim, AllShiftOpsPreserveLhsSignedness) {
  SimFixture f;
  MakeSignedVarAdv(f, "s", 8, 0x0F);
  MakeVar(f, "amt", 4, 1);

  TokenKind ops[] = {TokenKind::kLtLt, TokenKind::kGtGt, TokenKind::kLtLtLt,
                     TokenKind::kGtGtGt};
  for (auto op : ops) {
    auto* expr = MakeBinary(f.arena, op, MakeId(f.arena, "s"),
                            MakeId(f.arena, "amt"));
    auto result = EvalExpr(expr, f.ctx, f.arena);
    EXPECT_TRUE(result.is_signed);
  }
}

// §11.4.10: Shift by zero returns the operand unchanged.
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

// §11.4.10: Shift amount larger than width produces zero (for left/logical
// right shifts) or all-ones (for arithmetic right shift of negative signed).
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

TEST(AlwaysCombExtendedSim, AlwaysCombLeftShift) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data, y;\n"
      "  always_comb y = data << 2;\n"
      "  initial begin\n"
      "    data = 8'h0F;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);

  EXPECT_EQ(y->value.ToUint64(), 0x3Cu);
}

TEST(AlwaysCombExtendedSim, AlwaysCombRightShift) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data, y;\n"
      "  always_comb y = data >> 4;\n"
      "  initial begin\n"
      "    data = 8'hF0;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);

  EXPECT_EQ(y->value.ToUint64(), 0x0Fu);
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
