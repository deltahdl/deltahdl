#include <gtest/gtest.h>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "lexer/token.h"
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
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer n, zero, div4;\n"
      "  initial begin\n"
      "    n = 8;\n"
      "    zero = 0;\n"
      "    div4 = n / zero + n;\n"
      "  end\n"
      "endmodule\n",
      f, "div4");
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

TEST(StateOps, TwoStateOperandsGiveKnownResult) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int n, sum;\n"
      "  initial begin\n"
      "    n = 8;\n"
      "    sum = n + n;\n"
      "  end\n"
      "endmodule\n",
      f, "sum");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 16u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
}

TEST(StateOps, MixedArithInFourStateDestPreservesX) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "res");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

TEST(StateOps, MixedBitwiseOrInFourStateDestPreservesUnknown) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int n;\n"
      "  integer res;\n"
      "  initial begin\n"
      "    n = 8;\n"
      "    res = 4'b01xz | n;\n"
      "  end\n"
      "endmodule\n",
      f, "res");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

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

TEST(StateOps, ModuloByZeroPreservedInInteger) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer n, zero, m;\n"
      "  initial begin\n"
      "    n = 7;\n"
      "    zero = 0;\n"
      "    m = n % zero;\n"
      "  end\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

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

TEST(StateOps, UnsignedDivideByZeroPreservedInLogic) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] a, b;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    a = 20;\n"
      "    b = 0;\n"
      "    q = a / b;\n"
      "  end\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

TEST(StateOps, UnsignedModuloByZeroPreservedInLogic) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] a, b;\n"
      "  logic [7:0] m;\n"
      "  initial begin\n"
      "    a = 20;\n"
      "    b = 0;\n"
      "    m = a % b;\n"
      "  end\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

}  // namespace
