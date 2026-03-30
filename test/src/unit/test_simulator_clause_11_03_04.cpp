#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StateOps, TwoStatePlusTwoState) {
  SimFixture f;
  MakeVar(f, "a", 8, 3);
  MakeVar(f, "b", 8, 5);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPlus,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 8u);
}

TEST(StateOps, TwoStateDivByZeroProducesX) {
  SimFixture f;
  MakeVar(f, "a", 8, 10);
  MakeVar(f, "b", 8, 0);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kSlash,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_FALSE(result.IsKnown());
}

TEST(StateOps, ModByZeroProducesX) {
  SimFixture f;
  MakeVar(f, "a", 8, 10);
  MakeVar(f, "b", 8, 0);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPercent,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_FALSE(result.IsKnown());
}

TEST(StateOps, MixedStateAddTreatedAsFourState) {
  SimFixture f;
  MakeVar(f, "a", 8, 5);
  auto* b_var = MakeVar(f, "b", 8, 0);
  b_var->value.words[0] = {~uint64_t{0}, ~uint64_t{0}};  // all-x
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPlus,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_FALSE(result.IsKnown());
}

TEST(StateOps, MixedStateBitwiseOrTreatedAsFourState) {
  SimFixture f;
  MakeVar(f, "a", 8, 0xFF);
  auto* b_var = MakeVar(f, "b", 8, 0);
  b_var->value.words[0].bval = 0xFF;  // all-x in low 8 bits
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPipe,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  // OR with all-ones known bits should produce all-ones regardless of x.
  EXPECT_EQ(result.words[0].aval & 0xFF, 0xFFu);
}

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

TEST(StateOps, TwoStateDivisionResult) {
  SimFixture f;
  MakeVar(f, "a", 8, 20);
  MakeVar(f, "b", 8, 4);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kSlash,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.ToUint64(), 5u);
}

TEST(StateOps, XPlusKnownProducesX) {
  SimFixture f;
  auto* a_var = MakeVar(f, "a", 8, 0);
  a_var->value.words[0] = {0, ~uint64_t{0}};  // all-x
  MakeVar(f, "b", 8, 8);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPlus,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_FALSE(result.IsKnown());
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

}  // namespace
