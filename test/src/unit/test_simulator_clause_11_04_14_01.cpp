#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// --- Left-to-right processing, append to right-hand end of generic stream ---

TEST(StreamExpressionConcat, StreamingMultipleElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {>> {4'hA, 4'h5}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(StreamExpressionConcat, PackAsAssignmentSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "    b = 8'hCD;\n"
      "    dst = {>> {a, b}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

TEST(StreamExpressionConcat, ThreeElementsLeftToRight) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [23:0] dst;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'h11;\n"
      "    b = 8'h22;\n"
      "    c = 8'h33;\n"
      "    dst = {>> {a, b, c}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x112233u);
}

TEST(StreamExpressionConcat, UnequalWidthElementsLeftToRight) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [11:0] dst;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] b;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "    b = 4'hC;\n"
      "    dst = {>> {a, b}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCu);
}

// --- Branch 1: bit-stream type expression ---

TEST(StreamExpressionConcat, PackSingleElementPreservesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'h5A;\n"
      "    b = {>> {a}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5Au);
}

TEST(StreamExpressionConcat, LiteralExpressionAppended) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] dst;\n"
      "  initial dst = {>> {8'hDE, 8'hAD}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADu);
}

TEST(StreamExpressionConcat, NestedStreamingConcatAsElement) {
  SimFixture f;

  MakeVar(f, "a", 8, 0xAB);
  MakeVar(f, "b", 8, 0xCD);

  auto* inner = f.arena.Create<Expr>();
  inner->kind = ExprKind::kStreamingConcat;
  inner->op = TokenKind::kGtGt;
  inner->elements.push_back(MakeId(f.arena, "a"));

  auto* outer = f.arena.Create<Expr>();
  outer->kind = ExprKind::kStreamingConcat;
  outer->op = TokenKind::kGtGt;
  outer->elements.push_back(inner);
  outer->elements.push_back(MakeId(f.arena, "b"));

  auto result = EvalExpr(outer, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0xABCDu);
}

TEST(StreamExpressionConcat, NestedStreamingConcatBitStreamCast) {
  SimFixture f;

  MakeVar(f, "x", 16, 0xABCD);

  auto* inner = f.arena.Create<Expr>();
  inner->kind = ExprKind::kStreamingConcat;
  inner->op = TokenKind::kLtLt;
  auto* ss = f.arena.Create<Expr>();
  ss->kind = ExprKind::kIntegerLiteral;
  ss->text = "8";
  ss->int_val = 8;
  inner->lhs = ss;
  inner->elements.push_back(MakeId(f.arena, "x"));

  auto inner_result = EvalExpr(inner, f.ctx, f.arena);
  EXPECT_EQ(inner_result.ToUint64(), 0xCDABu);

  auto* outer = f.arena.Create<Expr>();
  outer->kind = ExprKind::kStreamingConcat;
  outer->op = TokenKind::kGtGt;
  outer->elements.push_back(inner);

  auto result = EvalExpr(outer, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0xCDABu);
}

// --- Branch 2: unpacked array → apply to each element ---

TEST(StreamExpressionConcat, StreamingUnpackedArrayConcat) {
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

TEST(StreamExpressionConcat, StreamingUnpackedArrayLeftShift) {
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

TEST(StreamExpressionConcat, StreamingUnpackedArrayMissingElemGivesX) {
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

TEST(StreamExpressionConcat, UnpackedArrayThreeElements) {
  SimFixture f;

  MakeVar(f, "d[0]", 8, 0x11);
  MakeVar(f, "d[1]", 8, 0x22);
  MakeVar(f, "d[2]", 8, 0x33);
  ArrayInfo info{};
  info.lo = 0;
  info.size = 3;
  info.elem_width = 8;
  f.ctx.RegisterArray("d", info);

  auto* stream = f.arena.Create<Expr>();
  stream->kind = ExprKind::kStreamingConcat;
  stream->op = TokenKind::kGtGt;
  stream->elements.push_back(MakeId(f.arena, "d"));
  auto result = EvalExpr(stream, f.ctx, f.arena);
  EXPECT_EQ(result.width, 24u);
  EXPECT_EQ(result.ToUint64(), 0x112233u);
}

TEST(StreamExpressionConcat, UnpackedArrayNonZeroLowBound) {
  SimFixture f;

  MakeVar(f, "e[3]", 8, 0xAA);
  MakeVar(f, "e[4]", 8, 0xBB);
  ArrayInfo info{};
  info.lo = 3;
  info.size = 2;
  info.elem_width = 8;
  f.ctx.RegisterArray("e", info);

  auto* stream = f.arena.Create<Expr>();
  stream->kind = ExprKind::kStreamingConcat;
  stream->op = TokenKind::kGtGt;
  stream->elements.push_back(MakeId(f.arena, "e"));
  auto result = EvalExpr(stream, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0xAABBu);
}

TEST(StreamExpressionConcat, UnpackedArrayMixedWithScalar) {
  SimFixture f;

  MakeVar(f, "s", 8, 0xFF);
  MakeVar(f, "g[0]", 8, 0x11);
  MakeVar(f, "g[1]", 8, 0x22);
  ArrayInfo info{};
  info.lo = 0;
  info.size = 2;
  info.elem_width = 8;
  f.ctx.RegisterArray("g", info);

  auto* stream = f.arena.Create<Expr>();
  stream->kind = ExprKind::kStreamingConcat;
  stream->op = TokenKind::kGtGt;
  stream->elements.push_back(MakeId(f.arena, "s"));
  stream->elements.push_back(MakeId(f.arena, "g"));

  auto result = EvalExpr(stream, f.ctx, f.arena);
  EXPECT_EQ(result.width, 24u);
  EXPECT_EQ(result.ToUint64(), 0xFF1122u);
}

TEST(StreamExpressionConcat, UnpackedArraySingleElement) {
  SimFixture f;

  MakeVar(f, "h[0]", 16, 0xBEEF);
  ArrayInfo info{};
  info.lo = 0;
  info.size = 1;
  info.elem_width = 16;
  f.ctx.RegisterArray("h", info);

  auto* stream = f.arena.Create<Expr>();
  stream->kind = ExprKind::kStreamingConcat;
  stream->op = TokenKind::kGtGt;
  stream->elements.push_back(MakeId(f.arena, "h"));
  auto result = EvalExpr(stream, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0xBEEFu);
}

// --- Edge cases ---

TEST(StreamExpressionConcat, EmptyStreamReturnsMinWidth) {
  SimFixture f;

  auto* stream = f.arena.Create<Expr>();
  stream->kind = ExprKind::kStreamingConcat;
  stream->op = TokenKind::kGtGt;

  auto result = EvalExpr(stream, f.ctx, f.arena);
  EXPECT_GE(result.width, 1u);
}

TEST(StreamExpressionConcat, ScalarAfterArrayAppendsToRight) {
  SimFixture f;

  MakeVar(f, "m[0]", 8, 0xAA);
  MakeVar(f, "m[1]", 8, 0xBB);
  ArrayInfo info{};
  info.lo = 0;
  info.size = 2;
  info.elem_width = 8;
  f.ctx.RegisterArray("m", info);
  MakeVar(f, "t", 8, 0xCC);

  auto* stream = f.arena.Create<Expr>();
  stream->kind = ExprKind::kStreamingConcat;
  stream->op = TokenKind::kGtGt;
  stream->elements.push_back(MakeId(f.arena, "m"));
  stream->elements.push_back(MakeId(f.arena, "t"));

  auto result = EvalExpr(stream, f.ctx, f.arena);
  EXPECT_EQ(result.width, 24u);
  EXPECT_EQ(result.ToUint64(), 0xAABBCCu);
}

}  // namespace
