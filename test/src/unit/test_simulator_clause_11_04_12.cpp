#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(EvalOp, ConcatXZPropagation) {
  SimFixture f;

  MakeVar4(f, "ca", 4, 0b1001, 0b0101);

  auto* bv = f.ctx.CreateVariable("cb", 4);
  bv->value = MakeLogic4VecVal(f.arena, 4, 0b0101);

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "ca"));
  concat->elements.push_back(MakeId(f.arena, "cb"));

  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);

  EXPECT_EQ(result.words[0].aval, 0x95u);
  EXPECT_EQ(result.words[0].bval, 0x50u);
}

TEST(EvalOp, ConcatWidthIsSumOfElements) {
  SimFixture f;

  auto* va = f.ctx.CreateVariable("a", 8);
  va->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* vb = f.ctx.CreateVariable("b", 4);
  vb->value = MakeLogic4VecVal(f.arena, 4, 0xC);

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "a"));
  concat->elements.push_back(MakeId(f.arena, "b"));

  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(result.width, 12u);
  EXPECT_EQ(result.ToUint64(), 0xABCu);
}

TEST(EvalOp, ConcatPartSelectUsesPackedRangeNMinus1Down0) {
  SimFixture f;

  auto* va = f.ctx.CreateVariable("hi", 4);
  va->value = MakeLogic4VecVal(f.arena, 4, 0xA);
  auto* vb = f.ctx.CreateVariable("lo", 4);
  vb->value = MakeLogic4VecVal(f.arena, 4, 0x5);

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "hi"));
  concat->elements.push_back(MakeId(f.arena, "lo"));

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = concat;
  sel->index = MakeInt(f.arena, 5);
  sel->index_end = MakeInt(f.arena, 2);

  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 0x9u);
}

TEST(EvalOp, ConcatBitSelectUsesPackedRangeNMinus1Down0) {
  SimFixture f;

  auto* va = f.ctx.CreateVariable("hi", 4);
  va->value = MakeLogic4VecVal(f.arena, 4, 0x8);
  auto* vb = f.ctx.CreateVariable("lo", 4);
  vb->value = MakeLogic4VecVal(f.arena, 4, 0x1);

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "hi"));
  concat->elements.push_back(MakeId(f.arena, "lo"));

  auto* sel_msb = MakeSelectExpr(f.arena, concat, MakeInt(f.arena, 7));
  auto msb = EvalExpr(sel_msb, f.ctx, f.arena);
  EXPECT_EQ(msb.ToUint64(), 1u);

  auto* sel_lsb = MakeSelectExpr(f.arena, concat, MakeInt(f.arena, 0));
  auto lsb = EvalExpr(sel_lsb, f.ctx, f.arena);
  EXPECT_EQ(lsb.ToUint64(), 1u);

  auto* sel_mid = MakeSelectExpr(f.arena, concat, MakeInt(f.arena, 4));
  auto mid = EvalExpr(sel_mid, f.ctx, f.arena);
  EXPECT_EQ(mid.ToUint64(), 0u);
}

}  // namespace
