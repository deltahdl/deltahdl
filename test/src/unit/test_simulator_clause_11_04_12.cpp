#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(EvalOp, Replicate3Times) {
  SimFixture f;

  auto* var = f.ctx.CreateVariable("v", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0xA);

  auto* rep = f.arena.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = MakeInt(f.arena, 3);
  rep->elements.push_back(MakeId(f.arena, "v"));
  auto result = EvalExpr(rep, f.ctx, f.arena);

  EXPECT_EQ(result.width, 12u);
  EXPECT_EQ(result.ToUint64(), 0xAAAu);
}

TEST(EvalOp, ReplicateOnce) {
  SimFixture f;

  auto* rep = f.arena.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = MakeInt(f.arena, 1);
  rep->elements.push_back(MakeInt(f.arena, 42));
  auto result = EvalExpr(rep, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

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

TEST(EvalOp, ReplicateXZPropagation) {
  SimFixture f;

  MakeVar4(f, "rv", 4, 0b1001, 0b0101);

  auto* rep = f.arena.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = MakeInt(f.arena, 2);
  rep->elements.push_back(MakeId(f.arena, "rv"));

  auto result = EvalExpr(rep, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);

  EXPECT_EQ(result.words[0].aval, 0x99u);
  EXPECT_EQ(result.words[0].bval, 0x55u);
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

TEST(EvalOp, ConcatSingleElement) {
  SimFixture f;

  auto* va = f.ctx.CreateVariable("s", 8);
  va->value = MakeLogic4VecVal(f.arena, 8, 0x42);

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "s"));

  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0x42u);
}

TEST(EvalOp, ConcatFourElements) {
  SimFixture f;

  auto* v1 = f.ctx.CreateVariable("p", 4);
  v1->value = MakeLogic4VecVal(f.arena, 4, 0xA);
  auto* v2 = f.ctx.CreateVariable("q", 4);
  v2->value = MakeLogic4VecVal(f.arena, 4, 0xB);
  auto* v3 = f.ctx.CreateVariable("r", 4);
  v3->value = MakeLogic4VecVal(f.arena, 4, 0xC);
  auto* v4 = f.ctx.CreateVariable("t", 4);
  v4->value = MakeLogic4VecVal(f.arena, 4, 0xD);

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "p"));
  concat->elements.push_back(MakeId(f.arena, "q"));
  concat->elements.push_back(MakeId(f.arena, "r"));
  concat->elements.push_back(MakeId(f.arena, "t"));

  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0xABCDu);
}

TEST(EvalOp, ConcatBitOrdering) {
  SimFixture f;

  auto* va = f.ctx.CreateVariable("hi", 8);
  va->value = MakeLogic4VecVal(f.arena, 8, 0xFF);
  auto* vb = f.ctx.CreateVariable("lo", 8);
  vb->value = MakeLogic4VecVal(f.arena, 8, 0x00);

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "hi"));
  concat->elements.push_back(MakeId(f.arena, "lo"));

  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0xFF00u);
}

}  // namespace
