#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/compiled_sim.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// Drives the runtime expression evaluator with two signed integer operands so
// that the signed arithmetic path in production is exercised, returning the
// evaluated result. The operands are plain signed variables; the rule under
// test is applied by EvalExpr, not by this setup.
Logic4Vec EvalSignedBin(SimFixture& f, TokenKind op, int64_t a, int64_t b,
                        uint32_t width = 8) {
  auto* va = f.ctx.CreateVariable("a", width);
  va->value = MakeLogic4VecVal(f.arena, width, static_cast<uint64_t>(a));
  va->value.is_signed = true;
  va->is_signed = true;
  auto* vb = f.ctx.CreateVariable("b", width);
  vb->value = MakeLogic4VecVal(f.arena, width, static_cast<uint64_t>(b));
  vb->value.is_signed = true;
  vb->is_signed = true;
  auto* expr =
      MakeBinary(f.arena, op, MakeId(f.arena, "a"), MakeId(f.arena, "b"));
  return EvalExpr(expr, f.ctx, f.arena);
}

TEST(EvalOpXZ, AddWithXPropagatesX) {
  SimFixture f;

  MakeVar4(f, "ax", 4, 0b1000, 0b0100);
  auto* b = f.ctx.CreateVariable("a1", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 1);

  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "ax"),
                          MakeId(f.arena, "a1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, DivByZeroReturnsX) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kSlash, MakeInt(f.arena, 10),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ModByZeroReturnsX) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kPercent, MakeInt(f.arena, 10),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, SubtractWithXPropagatesX) {
  SimFixture f;

  MakeVar4(f, "sx", 4, 0b1000, 0b0100);
  auto* b = f.ctx.CreateVariable("s1", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kMinus, MakeId(f.arena, "sx"),
                          MakeId(f.arena, "s1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, MultiplyWithZPropagatesX) {
  SimFixture f;

  MakeVar4(f, "mz", 4, 0b1000, 0b0010);
  auto* b = f.ctx.CreateVariable("m3", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 3);
  auto* expr = MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "mz"),
                          MakeId(f.arena, "m3"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, PowerWithXPropagatesX) {
  SimFixture f;

  MakeVar4(f, "px", 4, 0b1000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 2),
                          MakeId(f.arena, "px"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, DivideWithXPropagatesX) {
  SimFixture f;

  MakeVar4(f, "dx", 4, 0b1000, 0b0100);
  auto* b = f.ctx.CreateVariable("d2", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kSlash, MakeId(f.arena, "dx"),
                          MakeId(f.arena, "d2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ModulusWithXPropagatesX) {
  SimFixture f;

  MakeVar4(f, "mx2", 4, 0b1000, 0b0100);
  auto* b = f.ctx.CreateVariable("m3", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 3);
  auto* expr = MakeBinary(f.arena, TokenKind::kPercent, MakeId(f.arena, "mx2"),
                          MakeId(f.arena, "m3"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, UnaryMinusWithXPropagatesX) {
  SimFixture f;

  MakeVar4(f, "umx", 4, 0b1000, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kMinus, MakeId(f.arena, "umx"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, UnaryPlusWithXPropagatesX) {
  SimFixture f;

  MakeVar4(f, "upx", 4, 0b1000, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kPlus, MakeId(f.arena, "upx"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, AddWithZPropagatesX) {
  SimFixture f;

  MakeVar4(f, "az", 4, 0b0100, 0b0100);
  auto* b = f.ctx.CreateVariable("z1", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "az"),
                          MakeId(f.arena, "z1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, MultiplyWithZBitPropagatesX) {
  SimFixture f;

  MakeVar4(f, "mz", 4, 0b0010, 0b0010);
  auto* b = f.ctx.CreateVariable("z3", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 3);
  auto* expr = MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "mz"),
                          MakeId(f.arena, "z3"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(OperatorSim, UnaryPlus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = +8'd42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(OperatorSim, UnaryMinus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = -8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(OperatorSim, BinaryAdd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd10 + 8'd20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(OperatorSim, BinarySub) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd30 - 8'd12;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 18u);
}

TEST(OperatorSim, BinaryMul) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd7 * 8'd6;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(OperatorSim, BinaryDiv) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd100 / 8'd5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(OperatorSim, BinaryMod) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd17 % 8'd5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(OperatorSim, BinaryPower) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd2 ** 8'd5;\n"
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

TEST(CompiledSim, ExecuteExpressionEval) {
  CompiledSimFixture f;
  auto* a_var = f.ctx.CreateVariable("a", 32);
  a_var->value = MakeLogic4VecVal(f.arena, 32, 10);
  auto* b_var = f.ctx.CreateVariable("b", 32);
  b_var->value = MakeLogic4VecVal(f.arena, 32, 20);
  auto* c_var = f.ctx.CreateVariable("c", 32);
  c_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kIdentifier;
  lhs->text = "c";
  auto* a_ref = f.arena.Create<Expr>();
  a_ref->kind = ExprKind::kIdentifier;
  a_ref->text = "a";
  auto* b_ref = f.arena.Create<Expr>();
  b_ref->kind = ExprKind::kIdentifier;
  b_ref->text = "b";
  auto* add = f.arena.Create<Expr>();
  add->kind = ExprKind::kBinary;
  add->op = TokenKind::kPlus;
  add->lhs = a_ref;
  add->rhs = b_ref;
  auto* assign = f.arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;
  assign->lhs = lhs;
  assign->rhs = add;

  auto* block = f.arena.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->stmts.push_back(assign);

  auto compiled = ProcessCompiler::Compile(1, block);
  compiled.Execute(f.ctx);
  EXPECT_EQ(c_var->value.ToUint64(), 30u);
}

TEST(EvalOp, PowerBasic) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 2),
                          MakeInt(f.arena, 10));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1024u);
}

TEST(EvalOp, PowerZeroExponent) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 5),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, PowerOneExponent) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 7),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 7u);
}

TEST(EvalOp, ZeroPowerZero) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 0),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, PowerBaseOneAnyExponent) {
  SimFixture f;

  auto* e1 = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 1),
                        MakeInt(f.arena, 100));
  EXPECT_EQ(EvalExpr(e1, f.ctx, f.arena).ToUint64(), 1u);

  auto* e2 = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 1),
                        MakeInt(f.arena, 0));
  EXPECT_EQ(EvalExpr(e2, f.ctx, f.arena).ToUint64(), 1u);
}

TEST(EvalOp, ModulusBasic) {
  SimFixture f;

  auto* e1 = MakeBinary(f.arena, TokenKind::kPercent, MakeInt(f.arena, 10),
                        MakeInt(f.arena, 3));
  EXPECT_EQ(EvalExpr(e1, f.ctx, f.arena).ToUint64(), 1u);

  auto* e2 = MakeBinary(f.arena, TokenKind::kPercent, MakeInt(f.arena, 11),
                        MakeInt(f.arena, 3));
  EXPECT_EQ(EvalExpr(e2, f.ctx, f.arena).ToUint64(), 2u);

  auto* e3 = MakeBinary(f.arena, TokenKind::kPercent, MakeInt(f.arena, 12),
                        MakeInt(f.arena, 3));
  EXPECT_EQ(EvalExpr(e3, f.ctx, f.arena).ToUint64(), 0u);
}

TEST(EvalOp, ZeroBasePositiveExponent) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 0),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, RealOperandPowerYieldsRealResult) {
  SimFixture f;
  MakeRealVar(f, "a", 9.0);
  MakeRealVar(f, "b", 0.5);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPower,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(ToDouble(result), 3.0);
}

TEST(EvalOp, NegativeBaseZeroExponentReturnsOne) {
  SimFixture f;

  auto* nb = f.ctx.CreateVariable("nb", 8);
  nb->value = MakeLogic4VecVal(f.arena, 8, 0xFD);
  nb->value.is_signed = true;
  nb->is_signed = true;
  auto* ze = f.ctx.CreateVariable("ze", 8);
  ze->value = MakeLogic4VecVal(f.arena, 8, 0);
  ze->value.is_signed = true;
  ze->is_signed = true;
  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeId(f.arena, "nb"),
                          MakeId(f.arena, "ze"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFF, 1u);
}

// Integer division truncates toward zero, not toward negative infinity, so a
// negative quotient rounds up to the smaller-magnitude integer.
TEST(EvalOp, SignedDivisionTruncatesTowardZero) {
  SimFixture f1;
  EXPECT_EQ(EvalSignedBin(f1, TokenKind::kSlash, -7, 2).ToUint64() & 0xFFu,
            static_cast<uint64_t>(-3) & 0xFFu);
  SimFixture f2;
  EXPECT_EQ(EvalSignedBin(f2, TokenKind::kSlash, 7, -2).ToUint64() & 0xFFu,
            static_cast<uint64_t>(-3) & 0xFFu);
}

// The modulus result carries the sign of the first operand regardless of the
// sign of the second operand.
TEST(EvalOp, SignedModulusTakesSignOfFirstOperand) {
  SimFixture f1;
  EXPECT_EQ(EvalSignedBin(f1, TokenKind::kPercent, -7, 2).ToUint64() & 0xFFu,
            static_cast<uint64_t>(-1) & 0xFFu);
  SimFixture f2;
  EXPECT_EQ(EvalSignedBin(f2, TokenKind::kPercent, 7, -2).ToUint64() & 0xFFu,
            1u);
}

// A zero base raised to a negative power yields an all-unknown result.
TEST(EvalOp, ZeroToNegativePowerReturnsX) {
  SimFixture f;
  auto result = EvalSignedBin(f, TokenKind::kPower, 0, -1);
  EXPECT_NE(result.words[0].bval, 0u);
}

// Table 11-4: a negative exponent over a nonzero base truncates the reciprocal
// to zero unless the base magnitude is one, where the sign follows the parity
// of the exponent.
TEST(EvalOp, IntegralPowerNegativeExponentRuntime) {
  SimFixture f1;
  EXPECT_EQ(EvalSignedBin(f1, TokenKind::kPower, 2, -1).ToUint64() & 0xFFu, 0u);
  SimFixture f2;
  EXPECT_EQ(EvalSignedBin(f2, TokenKind::kPower, 1, -5).ToUint64() & 0xFFu, 1u);
  SimFixture f3;
  EXPECT_EQ(EvalSignedBin(f3, TokenKind::kPower, -1, -3).ToUint64() & 0xFFu,
            static_cast<uint64_t>(-1) & 0xFFu);
  SimFixture f4;
  EXPECT_EQ(EvalSignedBin(f4, TokenKind::kPower, -1, -2).ToUint64() & 0xFFu,
            1u);
}

}  // namespace
