#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(EvalAdv, StreamingLeftShiftReversesSlices) {
  SimFixture f;

  MakeVar(f, "sv", 16, 0xABCD);
  auto* stream = f.arena.Create<Expr>();
  stream->kind = ExprKind::kStreamingConcat;
  stream->op = TokenKind::kLtLt;
  auto* size_expr = f.arena.Create<Expr>();
  size_expr->kind = ExprKind::kIntegerLiteral;
  size_expr->text = "8";
  size_expr->int_val = 8;
  stream->lhs = size_expr;
  stream->elements.push_back(MakeId(f.arena, "sv"));
  auto result = EvalExpr(stream, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xCDABu);
}

TEST(EvalAdv, StreamingRightShiftPreservesOrder) {
  SimFixture f;

  MakeVar(f, "sv2", 16, 0xABCD);
  auto* stream = f.arena.Create<Expr>();
  stream->kind = ExprKind::kStreamingConcat;
  stream->op = TokenKind::kGtGt;
  auto* size_expr = f.arena.Create<Expr>();
  size_expr->kind = ExprKind::kIntegerLiteral;
  size_expr->text = "8";
  size_expr->int_val = 8;
  stream->lhs = size_expr;
  stream->elements.push_back(MakeId(f.arena, "sv2"));
  auto result = EvalExpr(stream, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xABCDu);
}

TEST(EvalAdv, StreamingUnpackedArrayConcat) {
  SimFixture f;

  MakeVar(f, "arr[0]", 8, 0xAB);
  MakeVar(f, "arr[1]", 8, 0xCD);
  ArrayInfo info{};
  info.lo = 0;
  info.size = 2;
  info.elem_width = 8;
  f.ctx.RegisterArray("arr", info);

  auto* stream = f.arena.Create<Expr>();
  stream->kind = ExprKind::kStreamingConcat;
  stream->op = TokenKind::kGtGt;
  stream->elements.push_back(MakeId(f.arena, "arr"));
  auto result = EvalExpr(stream, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0xABCDu);
}

TEST(EvalAdv, StreamingUnpackedArrayLeftShift) {
  SimFixture f;

  MakeVar(f, "arr2[0]", 8, 0xAB);
  MakeVar(f, "arr2[1]", 8, 0xCD);
  ArrayInfo info{};
  info.lo = 0;
  info.size = 2;
  info.elem_width = 8;
  f.ctx.RegisterArray("arr2", info);

  auto* stream = f.arena.Create<Expr>();
  stream->kind = ExprKind::kStreamingConcat;
  stream->op = TokenKind::kLtLt;
  auto* size_expr = f.arena.Create<Expr>();
  size_expr->kind = ExprKind::kIntegerLiteral;
  size_expr->text = "8";
  size_expr->int_val = 8;
  stream->lhs = size_expr;
  stream->elements.push_back(MakeId(f.arena, "arr2"));
  auto result = EvalExpr(stream, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0xCDABu);
}

TEST(EvalAdv, StreamingUnpackedArrayMissingElemGivesX) {
  SimFixture f;

  MakeVar(f, "arr3[0]", 8, 0x11);
  MakeVar(f, "arr3[2]", 8, 0x33);
  ArrayInfo info{};
  info.lo = 0;
  info.size = 3;
  info.elem_width = 8;
  f.ctx.RegisterArray("arr3", info);

  auto* stream = f.arena.Create<Expr>();
  stream->kind = ExprKind::kStreamingConcat;
  stream->op = TokenKind::kGtGt;
  stream->elements.push_back(MakeId(f.arena, "arr3"));
  auto result = EvalExpr(stream, f.ctx, f.arena);
  EXPECT_EQ(result.width, 24u);

  EXPECT_EQ(result.ToUint64(), 0x110033u);
}

}
