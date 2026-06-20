#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(ExpressionBitLength, TernaryWidthFromBranches) {
  SimFixture f;

  auto* cond = f.ctx.CreateVariable("tc", 1);
  cond->value = MakeLogic4VecVal(f.arena, 1, 1);
  auto* tv = f.ctx.CreateVariable("tv", 8);
  tv->value = MakeLogic4VecVal(f.arena, 8, 0xFF);
  auto* fv = f.ctx.CreateVariable("fv", 4);
  fv->value = MakeLogic4VecVal(f.arena, 4, 0xA);
  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeId(f.arena, "tc");
  tern->true_expr = MakeId(f.arena, "tv");
  tern->false_expr = MakeId(f.arena, "fv");
  auto result = EvalExpr(tern, f.ctx, f.arena);

  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
}

TEST(ExpressionBitLength, AssignmentContextWidthSameSize) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  logic [15:0] sumA;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    sumA = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sumA");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0000u);
}

TEST(ExpressionBitLength, CastingSetsContextWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  logic [15:0] answer;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    answer = (a + b + 0) >> 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("answer");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x8000u);
}

TEST(ExpressionBitLength, CastWidensIntermediateValue) {
  SimFixture f;
  MakeVar(f, "x", 4, 0xF);

  auto* cast = f.arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = "int";
  cast->lhs = MakeId(f.arena, "x");

  auto result = EvalExpr(cast, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
  EXPECT_EQ(result.ToUint64(), 0xFu);
}

TEST(ExpressionBitLength, CastWidensOperandPreservesCarry) {
  SimFixture f;
  MakeVar(f, "a", 4, 0xF);
  MakeVar(f, "b", 4, 1);

  auto* cast = f.arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = "int";
  cast->lhs = MakeId(f.arena, "a");

  auto* add = MakeBinary(f.arena, TokenKind::kPlus, cast, MakeId(f.arena, "b"));

  auto result = EvalExpr(add, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 0x10u);
  EXPECT_EQ(result.width, 32u);
}

TEST(ExpressionBitLength, ShiftWidthIsLhsWidth) {
  SimFixture f;
  MakeVar(f, "sv", 8, 0xFF);
  MakeVar(f, "sh", 16, 2);

  for (TokenKind op : {TokenKind::kLtLt, TokenKind::kGtGt, TokenKind::kLtLtLt,
                       TokenKind::kGtGtGt}) {
    auto* expr =
        MakeBinary(f.arena, op, MakeId(f.arena, "sv"), MakeId(f.arena, "sh"));
    auto result = EvalExpr(expr, f.ctx, f.arena);
    EXPECT_EQ(result.width, 8u);
  }
}

TEST(ExpressionBitLength, PowerWidthIsBaseWidth) {
  SimFixture f;
  MakeVar(f, "base", 8, 3);
  MakeVar(f, "exp", 16, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeId(f.arena, "base"),
                          MakeId(f.arena, "exp"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 9u);
}

TEST(ExpressionBitLength, ReductionOpsProduceOneBit) {
  SimFixture f;
  MakeVar(f, "rv", 8, 0xFF);

  for (TokenKind op : {TokenKind::kAmp, TokenKind::kTildeAmp, TokenKind::kPipe,
                       TokenKind::kTildePipe, TokenKind::kCaret,
                       TokenKind::kTildeCaret, TokenKind::kCaretTilde}) {
    auto* expr = MakeUnary(f.arena, op, MakeId(f.arena, "rv"));
    auto result = EvalExpr(expr, f.ctx, f.arena);
    EXPECT_EQ(result.width, 1u);
  }
}

TEST(ExpressionBitLength, LogicalNotProducesOneBit) {
  SimFixture f;
  MakeVar(f, "nv", 16, 0);
  auto* expr = MakeUnary(f.arena, TokenKind::kBang, MakeId(f.arena, "nv"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ExpressionBitLength, LogicalAndOrProduceOneBit) {
  SimFixture f;
  MakeVar(f, "la", 16, 1);
  MakeVar(f, "lb", 8, 1);

  auto* and_expr = MakeBinary(f.arena, TokenKind::kAmpAmp,
                              MakeId(f.arena, "la"), MakeId(f.arena, "lb"));
  auto r1 = EvalExpr(and_expr, f.ctx, f.arena);
  EXPECT_EQ(r1.width, 1u);

  auto* or_expr = MakeBinary(f.arena, TokenKind::kPipePipe,
                             MakeId(f.arena, "la"), MakeId(f.arena, "lb"));
  auto r2 = EvalExpr(or_expr, f.ctx, f.arena);
  EXPECT_EQ(r2.width, 1u);
}

TEST(ExpressionBitLength, ImplicationAndEquivalenceProduceOneBit) {
  SimFixture f;
  MakeVar(f, "ia", 16, 1);
  MakeVar(f, "ib", 8, 0);

  auto* impl = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "ia"),
                          MakeId(f.arena, "ib"));
  auto r1 = EvalExpr(impl, f.ctx, f.arena);
  EXPECT_EQ(r1.width, 1u);
  EXPECT_EQ(r1.ToUint64(), 0u);

  auto* equiv = MakeBinary(f.arena, TokenKind::kLtDashGt, MakeId(f.arena, "ia"),
                           MakeId(f.arena, "ib"));
  auto r2 = EvalExpr(equiv, f.ctx, f.arena);
  EXPECT_EQ(r2.width, 1u);
  EXPECT_EQ(r2.ToUint64(), 0u);
}

TEST(ExpressionBitLength, ComparisonOpsProduceOneBit) {
  SimFixture f;
  MakeVar(f, "ca", 16, 5);
  MakeVar(f, "cb", 8, 5);

  for (TokenKind op : {TokenKind::kEqEq, TokenKind::kBangEq, TokenKind::kEqEqEq,
                       TokenKind::kBangEqEq, TokenKind::kLt, TokenKind::kGt,
                       TokenKind::kLtEq, TokenKind::kGtEq}) {
    auto* expr =
        MakeBinary(f.arena, op, MakeId(f.arena, "ca"), MakeId(f.arena, "cb"));
    auto result = EvalExpr(expr, f.ctx, f.arena);
    EXPECT_EQ(result.width, 1u);
  }
}

TEST(ExpressionBitLength, ShiftAmountIsSelfDetermined) {
  SimFixture f;
  MakeVar(f, "sd", 4, 0x8);
  MakeVar(f, "sa", 32, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtGt, MakeId(f.arena, "sd"),
                          MakeId(f.arena, "sa"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 4u);
}

TEST(ExpressionBitLength, TernaryConditionIsSelfDetermined) {
  SimFixture f;
  MakeVar(f, "tc32", 32, 1);
  MakeVar(f, "ttv", 4, 0xA);
  MakeVar(f, "tfv", 4, 0x5);

  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeId(f.arena, "tc32");
  tern->true_expr = MakeId(f.arena, "ttv");
  tern->false_expr = MakeId(f.arena, "tfv");
  auto result = EvalExpr(tern, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
}

TEST(ExpressionBitLength, ReplicationWidthIsCountTimesElement) {
  SimFixture f;
  MakeVar(f, "re", 8, 0xFF);
  auto* repl = f.arena.Create<Expr>();
  repl->kind = ExprKind::kReplicate;
  repl->repeat_count = MakeInt(f.arena, 3);
  repl->elements.push_back(MakeId(f.arena, "re"));
  auto result = EvalExpr(repl, f.ctx, f.arena);
  EXPECT_EQ(result.width, 24u);
}

TEST(ExpressionBitLength, UnsizedConstantLiteralYieldsAtLeast32Bits) {
  SimFixture f;
  auto* lit = MakeInt(f.arena, 42);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_GE(result.width, 32u);
}

TEST(ExpressionBitLength, SizedConstantLiteralYieldsGivenWidth) {
  SimFixture f;
  auto* lit = f.arena.Create<Expr>();
  lit->kind = ExprKind::kIntegerLiteral;
  lit->text = "8'hFF";
  lit->int_val = 0xFF;
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
}

TEST(ExpressionBitLength, ArithmeticResultUsesMaxOperandWidth) {
  SimFixture f;
  MakeVar(f, "aw8", 8, 0xFF);
  MakeVar(f, "bw16", 16, 0x0001);
  for (TokenKind op : {TokenKind::kPlus, TokenKind::kMinus, TokenKind::kStar,
                       TokenKind::kSlash, TokenKind::kPercent, TokenKind::kAmp,
                       TokenKind::kPipe, TokenKind::kCaret,
                       TokenKind::kCaretTilde, TokenKind::kTildeCaret}) {
    auto* expr = MakeBinary(f.arena, op, MakeId(f.arena, "aw8"),
                            MakeId(f.arena, "bw16"));
    auto result = EvalExpr(expr, f.ctx, f.arena);
    EXPECT_EQ(result.width, 16u);
  }
}

TEST(ExpressionBitLength, UnaryPlusMinusTildePreserveOperandWidth) {
  SimFixture f;
  MakeVar(f, "uw", 12, 0x123);
  for (TokenKind op :
       {TokenKind::kPlus, TokenKind::kMinus, TokenKind::kTilde}) {
    auto* expr = MakeUnary(f.arena, op, MakeId(f.arena, "uw"));
    auto result = EvalExpr(expr, f.ctx, f.arena);
    EXPECT_EQ(result.width, 12u);
  }
}

TEST(ExpressionBitLength, ConcatenationResultIsSumOfOperandWidths) {
  SimFixture f;
  MakeVar(f, "cca", 8, 0xAA);
  MakeVar(f, "ccb", 16, 0xBBCC);
  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements = {MakeId(f.arena, "cca"), MakeId(f.arena, "ccb")};
  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(result.width, 24u);
}

TEST(ExpressionBitLength, LogicalAndOperandIsSelfDetermined) {
  SimFixture f;
  MakeVar(f, "laa", 16, 0xFFFF);
  MakeVar(f, "lab", 16, 0x0001);
  auto* add = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "laa"),
                         MakeId(f.arena, "lab"));
  auto* one = MakeInt(f.arena, 1);
  auto* land = MakeBinary(f.arena, TokenKind::kAmpAmp, add, one);
  auto result = EvalExpr(land, f.ctx, f.arena, 64);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(ExpressionBitLength, ReductionXorOperandIsSelfDetermined) {
  SimFixture f;
  MakeVar(f, "rxa", 16, 0xFFFF);
  MakeVar(f, "rxb", 16, 0x0001);
  auto* add = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "rxa"),
                         MakeId(f.arena, "rxb"));
  auto* xor_reduce = MakeUnary(f.arena, TokenKind::kCaret, add);
  auto result = EvalExpr(xor_reduce, f.ctx, f.arena, 64);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(ExpressionBitLength, ConcatenationOperandIsSelfDetermined) {
  SimFixture f;
  MakeVar(f, "csa", 16, 0xFFFF);
  MakeVar(f, "csb", 16, 0x0001);
  auto* add = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "csa"),
                         MakeId(f.arena, "csb"));
  auto* one_bit = f.arena.Create<Expr>();
  one_bit->kind = ExprKind::kIntegerLiteral;
  one_bit->text = "1'b1";
  one_bit->int_val = 1;
  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements = {add, one_bit};
  auto result = EvalExpr(concat, f.ctx, f.arena, 64);
  EXPECT_EQ(result.width, 17u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ExpressionBitLength, ReplicationElementIsSelfDetermined) {
  SimFixture f;
  MakeVar(f, "rea", 16, 0xFFFF);
  MakeVar(f, "reb", 16, 0x0001);
  auto* add = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "rea"),
                         MakeId(f.arena, "reb"));
  auto* repl = f.arena.Create<Expr>();
  repl->kind = ExprKind::kReplicate;
  repl->repeat_count = MakeInt(f.arena, 2);
  repl->elements.push_back(add);
  auto result = EvalExpr(repl, f.ctx, f.arena, 64);
  EXPECT_EQ(result.width, 32u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
