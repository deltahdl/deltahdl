#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ExprType, DecimalLiteralIsSigned) {
  SimFixture f;
  auto* lit = MakeInt(f.arena, 42);
  lit->text = "42";
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  EXPECT_TRUE(result.is_signed);
}

TEST(ExprType, BasedLiteralIsUnsigned) {
  SimFixture f;
  auto* lit = MakeInt(f.arena, 0xA);
  lit->text = "8'hA";
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xAu);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, SignedBasedLiteralIsSigned) {
  SimFixture f;
  auto* lit = MakeInt(f.arena, 0xA);
  lit->text = "4'shA";
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
}

TEST(ExprType, UnsizedBasedUnsignedIsNotSigned) {
  SimFixture f;
  auto* lit = MakeInt(f.arena, 12);
  lit->text = "'d12";
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, UnsizedBasedSignedIsSigned) {
  SimFixture f;
  auto* lit = MakeInt(f.arena, 12);
  lit->text = "'sd12";
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
}

TEST(ExprType, MixedSignednessYieldsUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "s", 8, 5);
  MakeVar(f, "u", 8, 3);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPlus,
                                    MakeId(f.arena, "s"), MakeId(f.arena, "u")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 8u);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, AllSignedYieldsSigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "a", 8, 5);
  MakeSignedVarAdv(f, "b", 8, 3);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPlus,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 8u);
  EXPECT_TRUE(result.is_signed);
}

TEST(ExprType, BitSelectAlwaysUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "sv", 8, 0xFF);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "sv");
  sel->index = MakeInt(f.arena, 7);
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, ConcatAlwaysUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "x", 4, 0xF);
  MakeSignedVarAdv(f, "y", 4, 0xA);
  auto* cat = f.arena.Create<Expr>();
  cat->kind = ExprKind::kConcatenation;
  cat->elements.push_back(MakeId(f.arena, "x"));
  cat->elements.push_back(MakeId(f.arena, "y"));
  auto result = EvalExpr(cat, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, ComparisonAlwaysUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "p", 8, 10);
  MakeSignedVarAdv(f, "q", 8, 20);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kGt,
                                    MakeId(f.arena, "p"), MakeId(f.arena, "q")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, ReductionAlwaysUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "r", 8, 0xFF);
  auto result =
      EvalExpr(MakeUnary(f.arena, TokenKind::kPipe, MakeId(f.arena, "r")),
               f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, PartSelectAlwaysUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "ps", 8, 0xFF);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "ps");
  sel->index = MakeInt(f.arena, 0);
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 0xFu);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, RealPlusRealIsReal) {
  SimFixture f;
  MakeRealVar(f, "a", 2.5);
  MakeRealVar(f, "b", 1.5);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPlus,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(ToDouble(result), 4.0);
}

TEST(ExprType, RealTimesIntIsReal) {
  SimFixture f;
  MakeRealVar(f, "r", 2.5);
  auto* vi = f.ctx.CreateVariable("i", 32);
  vi->value = MakeLogic4VecVal(f.arena, 32, 3);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kStar,
                                    MakeId(f.arena, "r"), MakeId(f.arena, "i")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(ToDouble(result), 7.5);
}

TEST(ExprType, IntTimesRealIsReal) {
  SimFixture f;
  auto* vi = f.ctx.CreateVariable("i", 32);
  vi->value = MakeLogic4VecVal(f.arena, 32, 4);
  MakeRealVar(f, "r", 0.25);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kStar,
                                    MakeId(f.arena, "i"), MakeId(f.arena, "r")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(ToDouble(result), 1.0);
}

TEST(ExprType, RealMinusRealIsReal) {
  SimFixture f;
  MakeRealVar(f, "a", 5.0);
  MakeRealVar(f, "b", 2.25);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kMinus,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(ToDouble(result), 2.75);
}

TEST(ExprType, RealDivRealIsReal) {
  SimFixture f;
  MakeRealVar(f, "a", 7.5);
  MakeRealVar(f, "b", 2.5);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kSlash,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(ToDouble(result), 3.0);
}

TEST(ExprType, UnaryMinusOnRealIsReal) {
  SimFixture f;
  MakeRealVar(f, "a", 3.5);
  auto result = EvalExpr(MakeUnary(f.arena, TokenKind::kMinus,
                                   MakeId(f.arena, "a")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(ToDouble(result), -3.5);
}

TEST(ExprType, UnaryPlusOnRealIsReal) {
  SimFixture f;
  MakeRealVar(f, "a", 3.5);
  auto result = EvalExpr(MakeUnary(f.arena, TokenKind::kPlus,
                                   MakeId(f.arena, "a")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(ToDouble(result), 3.5);
}

TEST(ExprType, BasedBinaryLiteralIsUnsigned) {
  SimFixture f;
  auto* lit = MakeInt(f.arena, 5);
  lit->text = "4'b0101";
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, BasedOctalLiteralIsUnsigned) {
  SimFixture f;
  auto* lit = MakeInt(f.arena, 7);
  lit->text = "4'o7";
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, BasedDecimalLiteralIsUnsigned) {
  SimFixture f;
  auto* lit = MakeInt(f.arena, 9);
  lit->text = "4'd9";
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, EqualityAlwaysUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "a", 8, 5);
  MakeSignedVarAdv(f, "b", 8, 5);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kEqEq,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, InequalityAlwaysUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "a", 8, 5);
  MakeSignedVarAdv(f, "b", 8, 10);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kBangEq,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, CaseEqualityAlwaysUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "a", 8, 5);
  MakeSignedVarAdv(f, "b", 8, 5);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kEqEqEq,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, LessThanAlwaysUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "a", 8, 3);
  MakeSignedVarAdv(f, "b", 8, 7);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kLt,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, ReductionXorAlwaysUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "v", 8, 0xAA);
  auto result =
      EvalExpr(MakeUnary(f.arena, TokenKind::kCaret, MakeId(f.arena, "v")),
               f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, ReductionNandAlwaysUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "v", 8, 0xFF);
  auto result =
      EvalExpr(MakeUnary(f.arena, TokenKind::kTildeAmp, MakeId(f.arena, "v")),
               f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, ReductionNorAlwaysUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "v", 8, 0x00);
  auto result =
      EvalExpr(MakeUnary(f.arena, TokenKind::kTildePipe, MakeId(f.arena, "v")),
               f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, PartSelectFullRangeStillUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "v", 8, 0xFF);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "v");
  sel->index = MakeInt(f.arena, 0);
  sel->index_end = MakeInt(f.arena, 8);
  sel->is_part_select_plus = true;
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, TypeNotDeterminedByLhs) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic signed [7:0] s;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd200;\n"
      "    b = 8'd100;\n"
      "    s = a + b;\n"
      "  end\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(val, 44u);
}

TEST(ExprType, TypeNotDeterminedByLhsSignedTarget) {
  SimFixture f;
  MakeSignedVarAdv(f, "target", 16, 0);
  MakeVar(f, "u1", 8, 200);
  MakeVar(f, "u2", 8, 100);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPlus,
                                    MakeId(f.arena, "u1"),
                                    MakeId(f.arena, "u2")),
                         f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, SelfDeterminedReductionInsideLargerExpr) {
  SimFixture f;
  MakeSignedVarAdv(f, "a", 8, 0xFF);
  MakeSignedVarAdv(f, "b", 8, 3);
  auto* red = MakeUnary(f.arena, TokenKind::kAmp, MakeId(f.arena, "a"));
  auto* add = MakeBinary(f.arena, TokenKind::kPlus, red, MakeId(f.arena, "b"));
  auto red_result = EvalExpr(red, f.ctx, f.arena);
  EXPECT_EQ(red_result.width, 1u);
  EXPECT_FALSE(red_result.is_signed);
  auto add_result = EvalExpr(add, f.ctx, f.arena);
  EXPECT_EQ(add_result.ToUint64(), 4u);
}

TEST(ExprType, TernaryBothSignedYieldsSigned) {
  SimFixture f;
  MakeVar(f, "c", 1, 1);
  MakeSignedVarAdv(f, "t", 8, 10);
  MakeSignedVarAdv(f, "e", 8, 20);
  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeId(f.arena, "c");
  tern->true_expr = MakeId(f.arena, "t");
  tern->false_expr = MakeId(f.arena, "e");
  auto result = EvalExpr(tern, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 10u);
  EXPECT_TRUE(result.is_signed);
}

TEST(ExprType, TernaryMixedSignednessYieldsUnsigned) {
  SimFixture f;
  MakeVar(f, "c", 1, 0);
  MakeSignedVarAdv(f, "t", 8, 10);
  MakeVar(f, "e", 8, 20);
  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeId(f.arena, "c");
  tern->true_expr = MakeId(f.arena, "t");
  tern->false_expr = MakeId(f.arena, "e");
  auto result = EvalExpr(tern, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, TernaryTrueBranchSelectedMixedStillUnsigned) {
  SimFixture f;
  MakeVar(f, "c", 1, 1);
  MakeSignedVarAdv(f, "t", 8, 10);
  MakeVar(f, "e", 8, 20);
  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeId(f.arena, "c");
  tern->true_expr = MakeId(f.arena, "t");
  tern->false_expr = MakeId(f.arena, "e");
  auto result = EvalExpr(tern, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 10u);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, TernaryBothUnsignedYieldsUnsigned) {
  SimFixture f;
  MakeVar(f, "c", 1, 1);
  MakeVar(f, "t", 8, 10);
  MakeVar(f, "e", 8, 20);
  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeId(f.arena, "c");
  tern->true_expr = MakeId(f.arena, "t");
  tern->false_expr = MakeId(f.arena, "e");
  auto result = EvalExpr(tern, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 10u);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, ConcatOfUnsignedAlwaysUnsigned) {
  SimFixture f;
  MakeVar(f, "a", 4, 0x5);
  MakeVar(f, "b", 4, 0xA);
  auto* cat = f.arena.Create<Expr>();
  cat->kind = ExprKind::kConcatenation;
  cat->elements.push_back(MakeId(f.arena, "a"));
  cat->elements.push_back(MakeId(f.arena, "b"));
  auto result = EvalExpr(cat, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, MixedSignednessBitwiseYieldsUnsigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "s", 8, 0xFF);
  MakeVar(f, "u", 8, 0x0F);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kAmp,
                                    MakeId(f.arena, "s"), MakeId(f.arena, "u")),
                         f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, AllSignedBitwiseYieldsSigned) {
  SimFixture f;
  MakeSignedVarAdv(f, "a", 8, 0xFF);
  MakeSignedVarAdv(f, "b", 8, 0x0F);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kAmp,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
}

TEST(ExprType, ShiftPreservesLeftOperandSignedness) {
  SimFixture f;
  MakeSignedVarAdv(f, "s", 8, 0x80);
  MakeVar(f, "amt", 8, 1);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kLtLt,
                                    MakeId(f.arena, "s"),
                                    MakeId(f.arena, "amt")),
                         f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
}

TEST(ExprType, ShiftUnsignedLeftStaysUnsigned) {
  SimFixture f;
  MakeVar(f, "u", 8, 0x80);
  MakeSignedVarAdv(f, "amt", 8, 1);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kLtLt,
                                    MakeId(f.arena, "u"),
                                    MakeId(f.arena, "amt")),
                         f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
}

}  // namespace
