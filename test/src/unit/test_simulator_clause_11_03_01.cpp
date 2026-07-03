#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

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

// §11.3.1: for operators other than the single-bit ones, when an operand is
// shortreal and none is real, the result is shortreal. Observed end-to-end from
// a real shortreal declaration so the sum itself is computed at shortreal
// (single) precision, not merely truncated on assignment. 2^24 and 1.0 are each
// representable in a C float, but their sum 2^24+1 is not, so a shortreal sum
// rounds to 2^24 while the same sum in reals stays exact. Comparing the widened
// shortreal sum against the real sum makes the shortreal result type visible.
TEST(RealOperandResult, E2eShortrealArithResultIsShortreal) {
  auto v = RunAndGet(
      "module t;\n"
      "  shortreal a, b;\n"
      "  real w, wr;\n"
      "  logic rounded;\n"
      "  initial begin\n"
      "    a = 16777216.0;\n"
      "    b = 1.0;\n"
      "    w = a + b;\n"
      "    wr = 16777216.0 + 1.0;\n"
      "    rounded = (w != wr);\n"
      "  end\n"
      "endmodule\n",
      "rounded");
  EXPECT_EQ(v, 1u);
}

// §11.3.1: when one operand is real and another is shortreal, the real operand
// wins and the result is real (double), not shortreal. Driven end-to-end from a
// real and a shortreal declaration. 2^24+1 is exact in a C double but not a C
// float, so a real result preserves it whereas a shortreal result would round
// it to 2^24; observing 2^24+1 survives proves the result was real.
TEST(RealOperandResult, E2eRealOperandWinsOverShortreal) {
  auto v = RunAndGet(
      "module t;\n"
      "  real a, c;\n"
      "  shortreal b;\n"
      "  logic real_result;\n"
      "  initial begin\n"
      "    a = 16777216.0;\n"
      "    b = 1.0;\n"
      "    c = a + b;\n"
      "    real_result = (c == 16777217.0);\n"
      "  end\n"
      "endmodule\n",
      "real_result");
  EXPECT_EQ(v, 1u);
}

// §11.3.1: a real array element (the LRM's realarray[intval] form) is a valid
// real operand. Read end-to-end from a real unpacked array indexed by an int
// variable and used in a real arithmetic expression, the element carries its
// stored real value into the result.
TEST(RealOperandResult, E2eRealArrayElementIsRealOperand) {
  auto v = RunAndGetReal(
      "module t;\n"
      "  real arr[4];\n"
      "  real m;\n"
      "  int i;\n"
      "  initial begin\n"
      "    i = 1;\n"
      "    arr[i] = 4.0;\n"
      "    m = arr[i] * 2.0;\n"
      "  end\n"
      "endmodule\n",
      "m");
  EXPECT_DOUBLE_EQ(v, 8.0);
}

// §11.3.1: the single-bit result rule for relational operators applies to every
// real-variable type, including shortreal operands (not just real). Driven
// end-to-end from shortreal declarations so the comparison operates on 32-bit
// real values produced by the shortreal decl path.
TEST(RealOperandResult, E2eRelationalOnShortrealIsSingleBit) {
  auto v = RunAndGet(
      "module t;\n"
      "  shortreal a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 3.5;\n"
      "    b = 2.5;\n"
      "    r = a > b;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 1u);
}

// §11.3.1: when one operand is shortreal and the other is a (non-real) integer,
// no operand is real, so the result is shortreal. Driven end-to-end from a
// shortreal declaration and an integer literal operand. 2^24+1 is exact in a C
// double but not a C float, so a shortreal result rounds the sum to 2^24 while
// the reference real sum stays exact; the mismatch proves the mixed
// shortreal/integer result took shortreal (single) precision.
TEST(RealOperandResult, E2eShortrealIntArithResultIsShortreal) {
  auto v = RunAndGet(
      "module t;\n"
      "  shortreal a;\n"
      "  real w, wr;\n"
      "  logic rounded;\n"
      "  initial begin\n"
      "    a = 16777216.0;\n"
      "    w = a + 1;\n"
      "    wr = 16777216.0 + 1.0;\n"
      "    rounded = (w != wr);\n"
      "  end\n"
      "endmodule\n",
      "rounded");
  EXPECT_EQ(v, 1u);
}

}  // namespace
