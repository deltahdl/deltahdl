#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_array.h"
#include "helpers_eval_op.h"
#include "helpers_queue.h"
#include "parser/ast.h"
#include "simulator/adv_sim.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

using namespace delta;

static Expr* MakeRange(Arena& arena, Expr* lo, Expr* hi,
                       TokenKind op = TokenKind::kEof) {
  auto* r = arena.Create<Expr>();
  r->kind = ExprKind::kSelect;
  r->index = lo;
  r->index_end = hi;
  r->op = op;
  return r;
}

namespace {

TEST(EvalAdv, InsideAbsTolerance) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("at", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 10);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "at");
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 7),
                                       MakeInt(f.arena, 5),
                                       TokenKind::kPlusSlashMinus));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, InsideAbsToleranceMiss) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("am", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 20);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "am");
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 7),
                                       MakeInt(f.arena, 5),
                                       TokenKind::kPlusSlashMinus));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalAdv, InsideRelTolerance) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("rt", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 8);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "rt");
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 10),
                                       MakeInt(f.arena, 25),
                                       TokenKind::kPlusPercentMinus));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, InsideXOperand) {
  SimFixture f;

  MakeVar4(f, "ix", 4, 0b0000, 0b0100);

  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "ix");
  inside->elements.push_back(MakeInt(f.arena, 3));
  inside->elements.push_back(MakeInt(f.arena, 5));
  inside->elements.push_back(MakeInt(f.arena, 7));

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(ExpressionSim, InsideValueMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = 8'd5 inside {8'd3, 8'd5, 8'd7};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(EvalOp, InsideMatch) {
  SimFixture f;

  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 5);
  inside->elements.push_back(MakeInt(f.arena, 3));
  inside->elements.push_back(MakeInt(f.arena, 5));
  inside->elements.push_back(MakeInt(f.arena, 7));

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, InsideNoMatch) {
  SimFixture f;

  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 4);
  inside->elements.push_back(MakeInt(f.arena, 3));
  inside->elements.push_back(MakeInt(f.arena, 5));
  inside->elements.push_back(MakeInt(f.arena, 7));

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, InsideRange) {
  SimFixture f;

  auto* range = f.arena.Create<Expr>();
  range->kind = ExprKind::kSelect;
  range->index = MakeInt(f.arena, 3);
  range->index_end = MakeInt(f.arena, 7);

  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 5);
  inside->elements.push_back(range);

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, InsideRangeNoMatch) {
  SimFixture f;

  auto* range = f.arena.Create<Expr>();
  range->kind = ExprKind::kSelect;
  range->index = MakeInt(f.arena, 3);
  range->index_end = MakeInt(f.arena, 7);

  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 10);
  inside->elements.push_back(range);

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

static Expr* MakeDollar(Arena& arena) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = "$";
  return e;
}

TEST(EvalAdv, InsideDollarLowerBound) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("dv", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 5);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "dv");
  inside->elements.push_back(
      MakeRange(f.arena, MakeDollar(f.arena), MakeInt(f.arena, 10)));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, InsideDollarUpperBound) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("du", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 200);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "du");
  inside->elements.push_back(
      MakeRange(f.arena, MakeInt(f.arena, 100), MakeDollar(f.arena)));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, InsideRhsXActsAsDontCare) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("wv", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0b0101);

  auto* xval = f.arena.Create<Expr>();
  xval->kind = ExprKind::kIdentifier;
  xval->text = "xv";
  auto* xvar = f.ctx.CreateVariable("xv", 4);
  xvar->value = MakeLogic4Vec(f.arena, 4);
  xvar->value.words[0].aval = 0b0001;
  xvar->value.words[0].bval = 0b0110;

  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "wv");
  inside->elements.push_back(xval);

  auto result = EvalExpr(inside, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, InsideLhsXNotDontCare) {
  SimFixture f;

  MakeVar4(f, "lx", 4, 0b0001, 0b0100);

  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "lx");
  inside->elements.push_back(MakeInt(f.arena, 0b0101));

  auto result = EvalExpr(inside, f.ctx, f.arena);

  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOp, InsideRangeLoBoundaryInclusive) {
  SimFixture f;
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 3);
  inside->elements.push_back(
      MakeRange(f.arena, MakeInt(f.arena, 3), MakeInt(f.arena, 7)));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, InsideRangeHiBoundaryInclusive) {
  SimFixture f;
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 7);
  inside->elements.push_back(
      MakeRange(f.arena, MakeInt(f.arena, 3), MakeInt(f.arena, 7)));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, InsideInvertedRangeIsEmpty) {
  SimFixture f;
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 5);
  inside->elements.push_back(
      MakeRange(f.arena, MakeInt(f.arena, 10), MakeInt(f.arena, 3)));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, InsideRepeatedValuesMatch) {
  SimFixture f;
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 5);
  inside->elements.push_back(MakeInt(f.arena, 5));
  inside->elements.push_back(MakeInt(f.arena, 5));
  inside->elements.push_back(MakeInt(f.arena, 10));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, InsideOverlappingRangesMatch) {
  SimFixture f;
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 7);
  inside->elements.push_back(
      MakeRange(f.arena, MakeInt(f.arena, 5), MakeInt(f.arena, 10)));
  inside->elements.push_back(
      MakeRange(f.arena, MakeInt(f.arena, 3), MakeInt(f.arena, 8)));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, InsideOrReductionAmbiguous) {
  SimFixture f;

  MakeVar4(f, "ov", 4, 0b0000, 0b0100);

  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "ov");

  inside->elements.push_back(MakeInt(f.arena, 0b0100));

  inside->elements.push_back(MakeInt(f.arena, 0b1111));

  auto result = EvalExpr(inside, f.ctx, f.arena);

  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, InsideOrReductionMatchOverridesAmbiguous) {
  SimFixture f;

  MakeVar4(f, "om", 4, 0b0000, 0b0100);

  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "om");

  inside->elements.push_back(MakeInt(f.arena, 0b0100));

  inside->elements.push_back(
      MakeRange(f.arena, MakeInt(f.arena, 0), MakeInt(f.arena, 15)));

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, InsideRelToleranceTruncation) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("tt", 8);

  var->value = MakeLogic4VecVal(f.arena, 8, 6);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "tt");
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 7),
                                       MakeInt(f.arena, 25),
                                       TokenKind::kPlusPercentMinus));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, InsideRelToleranceTruncationMiss) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("tm", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 5);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "tm");
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 7),
                                       MakeInt(f.arena, 25),
                                       TokenKind::kPlusPercentMinus));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// §11.4.13: a set member naming an unpacked array is traversed down to its
// singular elements, so {1, 2, q} with q = '{3,4,5} behaves like {1,2,3,4,5}.
// Builds `ex inside {1, 2, q}` for a 32-bit `ex` holding `ex_val` and returns
// the evaluated match result; q is '{3,4,5}.
static uint64_t EvalInsideQueueMember(SimFixture& f, uint64_t ex_val) {
  MakeQueue(f, "q", {3, 4, 5});
  auto* var = f.ctx.CreateVariable("ex", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, ex_val);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "ex");
  inside->elements.push_back(MakeInt(f.arena, 1));
  inside->elements.push_back(MakeInt(f.arena, 2));
  inside->elements.push_back(MakeId(f.arena, "q"));
  return EvalExpr(inside, f.ctx, f.arena).ToUint64();
}

TEST(EvalOp, InsideQueueMemberDescends) {
  SimFixture f;
  EXPECT_EQ(EvalInsideQueueMember(f, 4), 1u);
}

TEST(EvalOp, InsideQueueMemberNoMatch) {
  SimFixture f;
  EXPECT_EQ(EvalInsideQueueMember(f, 9), 0u);
}

// A fixed-size unpacked array member descends the same way. MakeArray4 fills
// arr[0..3] with {10, 20, 30, 40}; only the descent can supply the match.
TEST(EvalOp, InsideFixedArrayMemberDescends) {
  SimFixture f;
  MakeArray4(f, "arr");
  auto* var = f.ctx.CreateVariable("fv", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 30);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "fv");
  inside->elements.push_back(MakeInt(f.arena, 5));
  inside->elements.push_back(MakeId(f.arena, "arr"));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, InsideFixedArrayMemberNoMatch) {
  SimFixture f;
  MakeArray4(f, "arr");
  auto* var = f.ctx.CreateVariable("fv", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 25);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "fv");
  inside->elements.push_back(MakeInt(f.arena, 5));
  inside->elements.push_back(MakeId(f.arena, "arr"));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
