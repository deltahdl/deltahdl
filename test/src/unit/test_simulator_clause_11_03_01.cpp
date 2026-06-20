#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// Builds a real-valued variable carried at shortreal (32-bit) precision. The
// shared MakeRealVar helper only produces 64-bit reals, so the shortreal result
// rule in §11.3.1 needs a narrower operand built locally.
Variable* MakeShortrealVar(SimFixture& f, std::string_view name, float val) {
  auto* var = f.ctx.CreateVariable(name, 32);
  uint32_t bits = 0;
  std::memcpy(&bits, &val, sizeof(float));
  var->value = MakeLogic4VecVal(f.arena, 32, bits);
  var->value.is_real = true;
  f.ctx.RegisterRealVariable(name);
  return var;
}

// Reinterprets the low 32 bits of a shortreal result as a float.
float ShortrealResult(const Logic4Vec& v) {
  auto bits = static_cast<uint32_t>(v.ToUint64());
  float val = 0.0f;
  std::memcpy(&val, &bits, sizeof(float));
  return val;
}

// Builds a conditional (a ? b : c) expression; no shared builder exists for it.
Expr* MakeTernary(Arena& arena, Expr* cond, Expr* t, Expr* f) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kTernary;
  e->condition = cond;
  e->true_expr = t;
  e->false_expr = f;
  return e;
}

TEST(RealOperandResult, RelationalLtOnRealIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "a", 1.5);
  MakeRealVar(f, "b", 2.5);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kLt,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RealOperandResult, RelationalGtOnRealIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "a", 3.0);
  MakeRealVar(f, "b", 2.0);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kGt,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RealOperandResult, RelationalLtEqOnRealIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "a", 2.0);
  MakeRealVar(f, "b", 2.0);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kLtEq,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RealOperandResult, RelationalGtEqOnRealIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "a", 1.0);
  MakeRealVar(f, "b", 2.0);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kGtEq,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(RealOperandResult, RelationalMixedRealIntIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "r", 2.5);
  MakeVar(f, "i", 32, 3);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kLt,
                                    MakeId(f.arena, "r"), MakeId(f.arena, "i")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RealOperandResult, LogicalAndOnRealIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "a", 1.5);
  MakeRealVar(f, "b", 2.5);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kAmpAmp,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RealOperandResult, LogicalOrOnRealIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "a", 0.0);
  MakeRealVar(f, "b", 2.5);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPipePipe,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RealOperandResult, LogicalNotOnRealIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "a", 0.0);
  auto result =
      EvalExpr(MakeUnary(f.arena, TokenKind::kBang, MakeId(f.arena, "a")),
               f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RealOperandResult, LogicalNotOnNonzeroRealIsFalse) {
  SimFixture f;
  MakeRealVar(f, "a", 3.14);
  auto result =
      EvalExpr(MakeUnary(f.arena, TokenKind::kBang, MakeId(f.arena, "a")),
               f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(RealOperandResult, EqualityOnRealIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "a", 2.5);
  MakeRealVar(f, "b", 2.5);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kEqEq,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RealOperandResult, InequalityOnRealIsSingleBit) {
  SimFixture f;
  MakeRealVar(f, "a", 2.5);
  MakeRealVar(f, "b", 3.0);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kBangEq,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RealOperandResult, E2eRealAddResult) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 1.5 + 2.25;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 3.75);
}

TEST(RealOperandResult, E2eRealSubResult) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 5.0 - 1.75;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 3.25);
}

TEST(RealOperandResult, E2eRealMulResult) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 2.5 * 4.0;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 10.0);
}

TEST(RealOperandResult, E2eRealDivResult) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 7.0 / 2.0;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 3.5);
}

TEST(RealOperandResult, E2eRelationalOnRealIsSingleBit) {
  auto v = RunAndGet(
      "module t;\n"
      "  real a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 3.14;\n"
      "    b = 2.71;\n"
      "    r = a > b;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 1u);
}

TEST(RealOperandResult, E2eLogicalAndOnRealIsSingleBit) {
  auto v = RunAndGet(
      "module t;\n"
      "  real a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 1.0;\n"
      "    b = 0.0;\n"
      "    r = a && b;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0u);
}

TEST(RealOperandResult, E2eUnaryMinusOnReal) {
  auto v = RunAndGetReal(
      "module t;\n"
      "  real a, b;\n"
      "  initial begin\n"
      "    a = 3.5;\n"
      "    b = -a;\n"
      "  end\n"
      "endmodule\n",
      "b");
  EXPECT_DOUBLE_EQ(v, -3.5);
}

TEST(RealOperandResult, E2eInsideOnRealIsSingleBit) {
  auto v = RunAndGet(
      "module t;\n"
      "  real a;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 2.0;\n"
      "    r = a inside {1.0, 2.0, 3.0};\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 1u);
}

TEST(RealOperandResult, E2eMixedRealIntArithResultIsReal) {
  auto v = RunAndGetReal(
      "module t;\n"
      "  real x;\n"
      "  initial x = 1.5 + 2;\n"
      "endmodule\n",
      "x");
  EXPECT_DOUBLE_EQ(v, 3.5);
}

// §11.3.1: for operators other than the single-bit ones, when no operand is
// real but an operand is shortreal, the result is shortreal (32-bit).
TEST(RealOperandResult, ShortrealArithResultIsShortreal) {
  SimFixture f;
  MakeShortrealVar(f, "a", 1.5f);
  MakeShortrealVar(f, "b", 2.25f);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPlus,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_EQ(result.width, 32u);
  EXPECT_FLOAT_EQ(ShortrealResult(result), 3.75f);
}

// §11.3.1: a real operand outranks a shortreal operand, so the result is real
// (64-bit) even when the other operand is only shortreal.
TEST(RealOperandResult, RealOperandWinsOverShortreal) {
  SimFixture f;
  MakeRealVar(f, "a", 1.5);
  MakeShortrealVar(f, "b", 2.25f);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kStar,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_EQ(result.width, 64u);
}

// §11.3.1: for the conditional operator a real selected branch makes the result
// real, so a chosen real arm produces a real result.
TEST(RealOperandResult, ConditionalWithRealBranchResultIsReal) {
  SimFixture f;
  MakeRealVar(f, "a", 1.5);
  MakeRealVar(f, "b", 2.5);
  auto result =
      EvalExpr(MakeTernary(f.arena, MakeInt(f.arena, 1), MakeId(f.arena, "a"),
                           MakeId(f.arena, "b")),
               f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
}

// §11.3.1: the operand before the ? is excluded when determining realness, so a
// real condition with integral arms yields an integral (non-real) result.
TEST(RealOperandResult, ConditionalConditionRealDoesNotForceRealResult) {
  SimFixture f;
  MakeRealVar(f, "rc", 1.5);
  MakeVar(f, "x", 32, 7);
  MakeVar(f, "y", 32, 9);
  auto result =
      EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "rc"), MakeId(f.arena, "x"),
                           MakeId(f.arena, "y")),
               f.ctx, f.arena);
  EXPECT_FALSE(result.is_real);
}

}  // namespace
