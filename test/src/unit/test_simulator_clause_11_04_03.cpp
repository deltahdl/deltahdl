#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/compiled_sim.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

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

TEST(EvalAdv, PowerNegativeExponentReturnsZero) {
  SimFixture f;

  MakeSignedVarAdv(f, "pb", 8, 3);

  MakeSignedVarAdv(f, "pe", 8, 0xFE);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "pb");
  expr->rhs = MakeId(f.arena, "pe");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalAdv, PowerZeroBaseNegativeExponentReturnsX) {
  SimFixture f;

  MakeSignedVarAdv(f, "zb", 8, 0);
  MakeSignedVarAdv(f, "ze", 8, 0xFF);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "zb");
  expr->rhs = MakeId(f.arena, "ze");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalAdv, PowerNegativeOneOddExponentReturnsNegativeOne) {
  SimFixture f;

  MakeSignedVarAdv(f, "n1", 8, 0xFF);
  MakeSignedVarAdv(f, "n3", 8, 3);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "n1");
  expr->rhs = MakeId(f.arena, "n3");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xFFu);
  EXPECT_TRUE(result.is_signed);
}

TEST(EvalAdv, PowerNegativeOneEvenExponentReturnsOne) {
  SimFixture f;

  MakeSignedVarAdv(f, "n1", 8, 0xFF);
  MakeSignedVarAdv(f, "n4", 8, 4);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "n1");
  expr->rhs = MakeId(f.arena, "n4");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_TRUE(result.is_signed);
}

TEST(EvalAdv, SignedDivisionTruncatesTowardZero) {
  SimFixture f;
  MakeSignedVarAdv(f, "sd", 8, 0xF9);
  MakeSignedVarAdv(f, "se", 8, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kSlash, MakeId(f.arena, "sd"),
                          MakeId(f.arena, "se"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xFDu);
  EXPECT_TRUE(result.is_signed);
}

TEST(EvalAdv, SignedModulusSignFollowsFirstOperand) {
  SimFixture f;
  MakeSignedVarAdv(f, "sm", 8, 0xF9);
  MakeSignedVarAdv(f, "sn", 8, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kPercent, MakeId(f.arena, "sm"),
                          MakeId(f.arena, "sn"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xFFu);
  EXPECT_TRUE(result.is_signed);
}

TEST(EvalAdv, SignedMultiplyNegativeOperand) {
  SimFixture f;
  MakeSignedVarAdv(f, "ma", 8, 0xFD);
  MakeSignedVarAdv(f, "mb", 8, 4);
  auto* expr = MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "ma"),
                          MakeId(f.arena, "mb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xF4u);
  EXPECT_TRUE(result.is_signed);
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

TEST(EvalAdv, UnsignedDivisionTruncates) {
  SimFixture f;
  auto* a = MakeVar(f, "ud", 8, 0xF9);
  (void)a;
  auto* b = MakeVar(f, "ue", 8, 2);
  (void)b;
  auto* expr = MakeBinary(f.arena, TokenKind::kSlash, MakeId(f.arena, "ud"),
                          MakeId(f.arena, "ue"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 124u);
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

TEST(EvalAdv, PowerNegativeBasePositiveExponent) {
  SimFixture f;

  MakeSignedVarAdv(f, "nb", 8, 0xFD);  // -3
  MakeSignedVarAdv(f, "ne", 8, 3);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "nb");
  expr->rhs = MakeId(f.arena, "ne");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // (-3) ** 3 = -27, in 8-bit two's complement: 0xE5
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xE5u);
  EXPECT_TRUE(result.is_signed);
}

TEST(EvalAdv, PowerNegativeBaseNegativeExponentReturnsZero) {
  SimFixture f;

  MakeSignedVarAdv(f, "nb2", 8, 0xFD);  // -3
  MakeSignedVarAdv(f, "ne2", 8, 0xFF);  // -1
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "nb2");
  expr->rhs = MakeId(f.arena, "ne2");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalAdv, PowerOneBaseNegativeExponentReturnsOne) {
  SimFixture f;

  MakeSignedVarAdv(f, "ob", 8, 1);
  MakeSignedVarAdv(f, "oe", 8, 0xFE);  // -2
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "ob");
  expr->rhs = MakeId(f.arena, "oe");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, PowerNegativeOneNegativeOddExponentReturnsNegativeOne) {
  SimFixture f;

  MakeSignedVarAdv(f, "n1a", 8, 0xFF);  // -1
  MakeSignedVarAdv(f, "n3a", 8, 0xFD);  // -3
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "n1a");
  expr->rhs = MakeId(f.arena, "n3a");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xFFu);
  EXPECT_TRUE(result.is_signed);
}

TEST(EvalAdv, PowerNegativeOneNegativeEvenExponentReturnsOne) {
  SimFixture f;

  MakeSignedVarAdv(f, "n1b", 8, 0xFF);  // -1
  MakeSignedVarAdv(f, "n4b", 8, 0xFC);  // -4
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "n1b");
  expr->rhs = MakeId(f.arena, "n4b");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_TRUE(result.is_signed);
}

TEST(EvalAdv, SignedModulusNegativeDivisor) {
  SimFixture f;

  MakeSignedVarAdv(f, "sm2", 8, 11);
  MakeSignedVarAdv(f, "sn2", 8, 0xFD);  // -3
  auto* expr = MakeBinary(f.arena, TokenKind::kPercent, MakeId(f.arena, "sm2"),
                          MakeId(f.arena, "sn2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // 11 % -3 = 2 (sign follows first operand, which is positive)
  EXPECT_EQ(result.ToUint64() & 0xFF, 2u);
  EXPECT_TRUE(result.is_signed);
}

TEST(EvalOp, ZeroBasePositiveExponent) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 0),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
