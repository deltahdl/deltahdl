#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// Builds a ternary expression `cond ? t : e` referencing existing variables by
// name. Shared by the TernaryX signedness tests, whose only differences are the
// variable declarations and the expected result.
Expr* MakeTernarySelect(SimFixture& f, const char* cond, const char* t,
                        const char* e) {
  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeId(f.arena, cond);
  tern->true_expr = MakeId(f.arena, t);
  tern->false_expr = MakeId(f.arena, e);
  return tern;
}

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
  auto result =
      EvalExpr(MakeUnary(f.arena, TokenKind::kMinus, MakeId(f.arena, "a")),
               f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(ToDouble(result), -3.5);
}

TEST(ExprType, UnaryPlusOnRealIsReal) {
  SimFixture f;
  MakeRealVar(f, "a", 3.5);
  auto result =
      EvalExpr(MakeUnary(f.arena, TokenKind::kPlus, MakeId(f.arena, "a")),
               f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(ToDouble(result), 3.5);
}

TEST(ExprType, RealCastToIntIsSigned) {
  SimFixture f;
  MakeRealVar(f, "r", 3.5);
  auto* cast = f.arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = "int";
  cast->lhs = MakeId(f.arena, "r");
  auto result = EvalExpr(cast, f.ctx, f.arena);
  EXPECT_FALSE(result.is_real);
  EXPECT_TRUE(result.is_signed);
}

TEST(ExprType, RealImplicitlyCoercedOnAssignIsSigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  int i;\n"
      "  initial begin\n"
      "    r = 3.75;\n"
      "    i = r;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("i");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.is_real);
  EXPECT_TRUE(var->value.is_signed);
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
  auto result = EvalExpr(MakeTernarySelect(f, "c", "t", "e"), f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 10u);
  EXPECT_TRUE(result.is_signed);
}

TEST(ExprType, TernaryMixedSignednessYieldsUnsigned) {
  SimFixture f;
  MakeVar(f, "c", 1, 0);
  MakeSignedVarAdv(f, "t", 8, 10);
  MakeVar(f, "e", 8, 20);
  auto result = EvalExpr(MakeTernarySelect(f, "c", "t", "e"), f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, TernaryTrueBranchSelectedMixedStillUnsigned) {
  SimFixture f;
  MakeVar(f, "c", 1, 1);
  MakeSignedVarAdv(f, "t", 8, 10);
  MakeVar(f, "e", 8, 20);
  auto result = EvalExpr(MakeTernarySelect(f, "c", "t", "e"), f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 10u);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, TernaryBothUnsignedYieldsUnsigned) {
  SimFixture f;
  MakeVar(f, "c", 1, 1);
  MakeVar(f, "t", 8, 10);
  MakeVar(f, "e", 8, 20);
  auto result = EvalExpr(MakeTernarySelect(f, "c", "t", "e"), f.ctx, f.arena);
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
  auto result =
      EvalExpr(MakeBinary(f.arena, TokenKind::kLtLt, MakeId(f.arena, "s"),
                          MakeId(f.arena, "amt")),
               f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
}

TEST(ExprType, ShiftUnsignedLeftStaysUnsigned) {
  SimFixture f;
  MakeVar(f, "u", 8, 0x80);
  MakeSignedVarAdv(f, "amt", 8, 1);
  auto result =
      EvalExpr(MakeBinary(f.arena, TokenKind::kLtLt, MakeId(f.arena, "u"),
                          MakeId(f.arena, "amt")),
               f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, ComparisonOfRealsIsUnsigned) {
  SimFixture f;
  MakeRealVar(f, "a", 1.5);
  MakeRealVar(f, "b", 2.5);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kLt,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_FALSE(result.is_real);
  EXPECT_FALSE(result.is_signed);
}

TEST(ExprType, PartSelectAssignedToWiderVarIsZeroExtended) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [15:0] a;\n"
      "  logic signed [7:0] b;\n"
      "  initial begin\n"
      "    b = 8'shFF;\n"
      "    a = b[7:0];\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(val, 0x00FFu);
}

// A based number (no 's') is unsigned, so when it is the source of an
// assignment to a wider signed target it is zero-extended, not sign-extended,
// even though its own high bit is set. Drives the §5.7.1 literal syntax through
// the full pipeline so the classification is observed via real assignment
// extension rather than an inspected flag.
TEST(ExprType, BasedLiteralUnsignedZeroExtendedFullPipeline) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic signed [15:0] w;\n"
      "  initial w = 8'h80;\n"
      "endmodule\n",
      "w");
  EXPECT_EQ(val, 0x0080u);
}

// The 's' notation flips the same literal to signed, so the identical value is
// now sign-extended into the wider target. This is the discriminating negative
// of the rule above and exercises the "except where s notation is used" branch.
TEST(ExprType, SignedBasedLiteralSignExtendedFullPipeline) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic signed [15:0] w;\n"
      "  initial w = 8'sh80;\n"
      "endmodule\n",
      "w");
  EXPECT_EQ(val, 0xFF80u);
}

// A bit-select result is unsigned regardless of the operand's signedness. The
// single selected bit of a signed vector, assigned to a wider signed target, is
// therefore zero-extended (result 0x0001); a signed 1-bit '1' would instead
// sign-extend to all ones. Built from §11.5.1 bit-select syntax end-to-end.
TEST(ExprType, BitSelectOfSignedIsUnsignedFullPipeline) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic signed [7:0] sv;\n"
      "  logic signed [15:0] w;\n"
      "  initial begin\n"
      "    sv = 8'shFF;\n"
      "    w = sv[7];\n"
      "  end\n"
      "endmodule\n",
      "w");
  EXPECT_EQ(val, 0x0001u);
}

// A concatenation result is unsigned regardless of its operands' signedness.
// Concatenating two signed nibbles yields an unsigned byte, so assignment to a
// wider signed target zero-extends (0x00FF); a signed byte would sign-extend to
// 0xFFFF. Built from §11.4.12 concatenation syntax end-to-end.
TEST(ExprType, ConcatOfSignedIsUnsignedFullPipeline) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic signed [3:0] a, b;\n"
      "  logic signed [15:0] w;\n"
      "  initial begin\n"
      "    a = 4'shF;\n"
      "    b = 4'shF;\n"
      "    w = {a, b};\n"
      "  end\n"
      "endmodule\n",
      "w");
  EXPECT_EQ(val, 0x00FFu);
}

// When all operands are signed the result is signed, so a signed sum that is
// narrower than its target sign-extends on assignment. Two signed bytes summing
// to -1 give 0xFFFF in a wider signed target; an unsigned result would instead
// zero-extend to 0x00FF. Operand signedness is taken from the `logic signed`
// declarations, driven end-to-end. Complements the unsigned-operand case in
// TypeNotDeterminedByLhs.
TEST(ExprType, AllSignedOperandsYieldSignedResultFullPipeline) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic signed [7:0] a, b;\n"
      "  logic signed [15:0] w;\n"
      "  initial begin\n"
      "    a = 8'shFE;\n"
      "    b = 8'sh01;\n"
      "    w = a + b;\n"
      "  end\n"
      "endmodule\n",
      "w");
  EXPECT_EQ(val, 0xFFFFu);
}

// If any operand is real the whole expression is real, so an integer multiplied
// by a real fraction keeps its fractional part instead of truncating to an
// integer. The int operand comes from a real declaration and the real result is
// read back through a real target, driven end-to-end.
TEST(ExprType, AnyRealOperandYieldsRealResultFullPipeline) {
  auto val = RunAndGetReal(
      "module t;\n"
      "  int i;\n"
      "  real w;\n"
      "  initial begin\n"
      "    i = 3;\n"
      "    w = i * 0.5;\n"
      "  end\n"
      "endmodule\n",
      "w");
  EXPECT_DOUBLE_EQ(val, 1.5);
}

// An unbased decimal literal is signed, so when it is the sole literal operand
// alongside a signed variable the whole addition stays signed and its narrower
// result sign-extends into the wider target. -2 + 1 gives -1 -> 0xFFFF; had the
// decimal literal been unsigned the mixed expression would be unsigned and
// yield 0x00FF. This observes the decimal-is-signed rule through a real literal
// operand end-to-end, distinct from the flag-only DecimalLiteralIsSigned.
TEST(ExprType, DecimalLiteralOperandIsSignedFullPipeline) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic signed [7:0] s;\n"
      "  logic signed [15:0] w;\n"
      "  initial begin\n"
      "    s = 8'shFE;\n"
      "    w = s + 1;\n"
      "  end\n"
      "endmodule\n",
      "w");
  EXPECT_EQ(val, 0xFFFFu);
}

}  // namespace
