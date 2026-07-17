#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StateOps, TwoStateSubtractResult) {
  SimFixture f;
  MakeVar(f, "a", 8, 10);
  MakeVar(f, "b", 8, 3);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kMinus,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.ToUint64(), 7u);
}

TEST(StateOps, TwoStateMultiplyResult) {
  SimFixture f;
  MakeVar(f, "a", 16, 6);
  MakeVar(f, "b", 16, 7);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kStar,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(StateOps, TwoStateBitwiseAndResult) {
  SimFixture f;
  MakeVar(f, "a", 8, 0xAA);
  MakeVar(f, "b", 8, 0x0F);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kAmp,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.ToUint64(), 0x0Au);
}

TEST(StateOps, TwoStateBitwiseXorResult) {
  SimFixture f;
  MakeVar(f, "a", 8, 0xAA);
  MakeVar(f, "b", 8, 0x55);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kCaret,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.ToUint64(), 0xFFu);
}

TEST(StateOps, TwoStateDivideResult) {
  SimFixture f;
  MakeVar(f, "a", 8, 20);
  MakeVar(f, "b", 8, 4);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kSlash,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.ToUint64(), 5u);
}

TEST(StateOps, TwoStateModuloResult) {
  SimFixture f;
  MakeVar(f, "a", 8, 23);
  MakeVar(f, "b", 8, 5);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPercent,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(StateOps, FourStateToTwoStateCoercionDivByZero) {
  auto result = RunAndGet(
      "module t;\n"
      "  int n, zero, div2;\n"
      "  initial begin\n"
      "    n = 8;\n"
      "    zero = 0;\n"
      "    div2 = n / zero + n;\n"
      "  end\n"
      "endmodule\n",
      "div2");
  EXPECT_EQ(result, 0u);
}

TEST(StateOps, FourStatePreservedInIntegerDivByZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer n, zero, div4;\n"
      "  initial begin\n"
      "    n = 8;\n"
      "    zero = 0;\n"
      "    div4 = n / zero + n;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("div4");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

TEST(StateOps, XCoercedToZeroInInt) {
  auto result = RunAndGet(
      "module t;\n"
      "  int dst;\n"
      "  initial dst = 'x + 8;\n"
      "endmodule\n",
      "dst");
  EXPECT_EQ(result, 0u);
}

TEST(StateOps, BitwiseOrWithXzLiteralCoercedToInt) {
  auto result = RunAndGet(
      "module t;\n"
      "  int n, res;\n"
      "  initial begin\n"
      "    n = 8;\n"
      "    res = 4'b01xz | n;\n"
      "  end\n"
      "endmodule\n",
      "res");
  EXPECT_EQ(result, 12u);
}

// Claim B, driven from real declarations: when both operands come from 2-state
// (int) variables, the result stays in the 2-state value set. This is the
// clause's "sum = n + n" line; a fully known 16 (never 0) shows the value is a
// real result rather than a coerced-away unknown.
TEST(StateOps, TwoStateOperandsGiveKnownResult) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int n, sum;\n"
      "  initial begin\n"
      "    n = 8;\n"
      "    sum = n + n;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("sum");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 16u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
}

// Claim A for arithmetic, observed uncoerced: an int (2-state) operand added to
// a logic (4-state) operand holding x evaluates as if all 4-state, so the
// result is unknown. A 4-state destination (integer) keeps the x visible rather
// than collapsing it to 0 the way an int destination would.
TEST(StateOps, MixedArithInFourStateDestPreservesX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  logic [31:0] u;\n"
      "  integer res;\n"
      "  initial begin\n"
      "    a = 5;\n"
      "    u = 'x;\n"
      "    res = a + u;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("res");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

// Claim A for bitwise OR, the uncoerced counterpart of the clause's res line:
// the same "4'b01xz | n" whose int destination coerced to 12 keeps its unknown
// bits when the destination is a 4-state integer, confirming the operation is
// carried out in the 4-state domain before any assignment coercion.
TEST(StateOps, MixedBitwiseOrInFourStateDestPreservesUnknown) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int n;\n"
      "  integer res;\n"
      "  initial begin\n"
      "    n = 8;\n"
      "    res = 4'b01xz | n;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("res");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

// Claim C, modulo-by-zero mirror of the div-by-zero example, into a 2-state
// destination: modulo is another operator that yields x for 2-state operands,
// and that x coerces to 0 when stored into an int.
TEST(StateOps, ModuloByZeroCoercedToZeroInInt) {
  auto result = RunAndGet(
      "module t;\n"
      "  int n, zero, m;\n"
      "  initial begin\n"
      "    n = 7;\n"
      "    zero = 0;\n"
      "    m = n % zero;\n"
      "  end\n"
      "endmodule\n",
      "m");
  EXPECT_EQ(result, 0u);
}

// Claim C, modulo-by-zero into a 4-state destination: the same exception keeps
// its unknown value when stored into an integer, the modulo counterpart of the
// div4 example.
TEST(StateOps, ModuloByZeroPreservedInInteger) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer n, zero, m;\n"
      "  initial begin\n"
      "    n = 7;\n"
      "    zero = 0;\n"
      "    m = n % zero;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("m");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

// Claim B for the unsigned 2-state operand type: two-state bit operands (unlike
// the signed int cases above) take the unsigned arithmetic path, and when both
// operands are known the result stays in the 2-state set. Driven from real bit
// declarations so the unsigned typing is what selects the path.
TEST(StateOps, TwoStateUnsignedOperandsGiveKnownResult) {
  auto result = RunAndGet(
      "module t;\n"
      "  bit [7:0] a, b, sum;\n"
      "  initial begin\n"
      "    a = 8;\n"
      "    b = 8;\n"
      "    sum = a + b;\n"
      "  end\n"
      "endmodule\n",
      "sum");
  EXPECT_EQ(result, 16u);
}

// Claim C via the unsigned path: division by zero with unsigned bit operands is
// the same x-producing exception, exercising the unsigned evaluator's zero
// guard rather than the signed one. A 4-state logic destination keeps the x
// visible.
TEST(StateOps, UnsignedDivideByZeroPreservedInLogic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] a, b;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    a = 20;\n"
      "    b = 0;\n"
      "    q = a / b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("q");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

// Claim C via the unsigned path, modulo counterpart: unsigned bit modulo by
// zero yields x through the unsigned evaluator's own zero guard, preserved in a
// logic destination.
TEST(StateOps, UnsignedModuloByZeroPreservedInLogic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] a, b;\n"
      "  logic [7:0] m;\n"
      "  initial begin\n"
      "    a = 20;\n"
      "    b = 0;\n"
      "    m = a % b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("m");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

}  // namespace
