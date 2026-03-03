// §11.4.3: Arithmetic operators

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// ==========================================================================
// Arithmetic X/Z propagation — §11.4.3
// ==========================================================================
TEST(EvalOpXZ, ArithAddX) {
  SimFixture f;
  // 4'b1x00 + 4'b0001 → all-X (any X/Z operand)
  MakeVar4(f, "ax", 4, 0b1000, 0b0100);  // 4'b1x00
  auto* b = f.ctx.CreateVariable("a1", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 1);

  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "ax"),
                          MakeId(f.arena, "a1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, DivByZeroReturnsX) {
  SimFixture f;
  // 10 / 0 → all-X (not 0)
  auto* expr = MakeBinary(f.arena, TokenKind::kSlash, MakeInt(f.arena, 10),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ModByZeroReturnsX) {
  SimFixture f;
  // 10 % 0 → all-X (not 0)
  auto* expr = MakeBinary(f.arena, TokenKind::kPercent, MakeInt(f.arena, 10),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, RealArithResult) {
  SimFixture f;
  MakeRealVar(f, "ra", 2.5);
  MakeRealVar(f, "rb", 1.5);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "ra"),
                          MakeId(f.arena, "rb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(ToDouble(result), 4.0);
}

TEST(EvalOpXZ, MixedRealIntArith) {
  SimFixture f;
  // If either operand is real, both are converted to real.
  MakeRealVar(f, "re", 2.5);
  auto* vi = f.ctx.CreateVariable("ri", 32);
  vi->value = MakeLogic4VecVal(f.arena, 32, 3);
  auto* expr = MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "re"),
                          MakeId(f.arena, "ri"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(ToDouble(result), 7.5);
}

// ==========================================================================
// Arithmetic X/Z — §11.4.3 (subtraction, multiply, power with X/Z)
// ==========================================================================
TEST(EvalOpXZ, ArithSubX) {
  SimFixture f;
  // 4'b1x00 - 1 → all-X (X/Z operand in subtraction)
  MakeVar4(f, "sx", 4, 0b1000, 0b0100);
  auto* b = f.ctx.CreateVariable("s1", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kMinus, MakeId(f.arena, "sx"),
                          MakeId(f.arena, "s1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ArithMulZ) {
  SimFixture f;
  // 4'b10z0 * 3 → all-X (Z operand in multiply)
  MakeVar4(f, "mz", 4, 0b1000, 0b0010);  // bit1=z (aval=0,bval=1)
  auto* b = f.ctx.CreateVariable("m3", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 3);
  auto* expr = MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "mz"),
                          MakeId(f.arena, "m3"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ArithPowX) {
  SimFixture f;
  // 2 ** 4'b1x00 → all-X (X in exponent)
  MakeVar4(f, "px", 4, 0b1000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 2),
                          MakeId(f.arena, "px"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// § expression — binary addition
TEST(SimA83, BinaryAddition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd3 + 8'd7;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// § expression — binary subtraction
TEST(SimA83, BinarySubtraction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd10 - 8'd3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// § expression — binary multiplication
TEST(SimA83, BinaryMultiplication) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd5 * 8'd6;\n"
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

// § expression — unary bitwise NOT
TEST(SimA83, UnaryNegate) {
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

// =============================================================================
// A.8.6 Operators — unary_operator — Simulation
// =============================================================================
// § unary_operator — unary plus (identity)
TEST(SimA86, UnaryPlus) {
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

// § unary_operator — unary minus (negate)
TEST(SimA86, UnaryMinus) {
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

// =============================================================================
// A.8.6 Operators — binary_operator (arithmetic) — Simulation
// =============================================================================
// § binary_operator — addition
TEST(SimA86, BinaryAdd) {
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

// § binary_operator — subtraction
TEST(SimA86, BinarySub) {
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

// § binary_operator — multiplication
TEST(SimA86, BinaryMul) {
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

// § binary_operator — division
TEST(SimA86, BinaryDiv) {
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

// § binary_operator — modulo
TEST(SimA86, BinaryMod) {
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

// § binary_operator — power
TEST(SimA86, BinaryPower) {
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

  // AST: c = a + b
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

TEST(EvalAdv, PowZeroExp) {
  SimFixture f;
  // a ** 0 = 1 for any a (Table 11-4).
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeInt(f.arena, 7);
  expr->rhs = MakeInt(f.arena, 0);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, PowNegExpInt) {
  SimFixture f;
  // 3 ** (-2) = 0 for integer (Table 11-4: |base|>1, negative exp → 0).
  MakeSignedVarAdv(f, "pb", 8, 3);
  // -2 in 8-bit signed = 0xFE
  MakeSignedVarAdv(f, "pe", 8, 0xFE);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "pb");
  expr->rhs = MakeId(f.arena, "pe");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalAdv, PowZeroBaseNegExp) {
  SimFixture f;
  // 0 ** (-1) = X (Table 11-4: zero base, negative exp → X).
  MakeSignedVarAdv(f, "zb", 8, 0);
  MakeSignedVarAdv(f, "ze", 8, 0xFF);  // -1 in 8-bit
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "zb");
  expr->rhs = MakeId(f.arena, "ze");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);  // result is X
}

TEST(EvalAdv, PowNeg1OddExp) {
  SimFixture f;
  // (-1) ** 3 = -1 (Table 11-4: base -1, odd exp).
  MakeSignedVarAdv(f, "n1", 8, 0xFF);  // -1 in 8-bit
  MakeSignedVarAdv(f, "n3", 8, 3);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "n1");
  expr->rhs = MakeId(f.arena, "n3");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xFFu);  // -1 in 8-bit
  EXPECT_TRUE(result.is_signed);
}

TEST(EvalAdv, PowNeg1EvenExp) {
  SimFixture f;
  // (-1) ** 4 = 1 (Table 11-4: base -1, even exp).
  MakeSignedVarAdv(f, "n1", 8, 0xFF);  // -1 in 8-bit
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

}  // namespace
