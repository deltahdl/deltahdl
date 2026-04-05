#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(StreamReordering, StreamingLeftShift) {
  SimFixture f;

  auto* var = f.ctx.CreateVariable("sv", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* sc = f.arena.Create<Expr>();
  sc->kind = ExprKind::kStreamingConcat;
  sc->op = TokenKind::kLtLt;
  sc->elements.push_back(MakeId(f.arena, "sv"));

  auto result = EvalExpr(sc, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 0xD5u);
}

TEST(StreamReordering, StreamingRightShift) {
  SimFixture f;

  auto* var = f.ctx.CreateVariable("sv2", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* sc = f.arena.Create<Expr>();
  sc->kind = ExprKind::kStreamingConcat;
  sc->op = TokenKind::kGtGt;
  sc->elements.push_back(MakeId(f.arena, "sv2"));

  auto result = EvalExpr(sc, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 0xABu);
}

TEST(StreamReordering, StreamingLeftShiftReversesSlices) {
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

TEST(StreamReordering, StreamingRightShiftPreservesOrder) {
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

TEST(StreamReordering, StreamingRightShiftIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {>> {8'hAB}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(StreamReordering, StreamingLeftShiftIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {<< {8'hAB}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xD5u);
}

// Req 3: Default slice_size (no lhs) shall equal explicit slice_size of 1.
TEST(StreamReordering, DefaultSliceSizeIsOne) {
  SimFixture f;

  MakeVar(f, "v", 8, 0xAB);

  auto* sc1 = f.arena.Create<Expr>();
  sc1->kind = ExprKind::kStreamingConcat;
  sc1->op = TokenKind::kLtLt;
  sc1->elements.push_back(MakeId(f.arena, "v"));
  auto r1 = EvalExpr(sc1, f.ctx, f.arena);

  auto* sc2 = f.arena.Create<Expr>();
  sc2->kind = ExprKind::kStreamingConcat;
  sc2->op = TokenKind::kLtLt;
  auto* ss = MakeInt(f.arena, 1);
  ss->text = "1";
  sc2->lhs = ss;
  sc2->elements.push_back(MakeId(f.arena, "v"));
  auto r2 = EvalExpr(sc2, f.ctx, f.arena);

  EXPECT_EQ(r1.ToUint64(), r2.ToUint64());
}

// Req 5: Type used as slice_size → block size is number of bits in that type.
TEST(StreamReordering, TypeSliceSizeReversesBytes) {
  SimFixture f;

  MakeVar(f, "v", 16, 0xABCD);
  auto* stream = f.arena.Create<Expr>();
  stream->kind = ExprKind::kStreamingConcat;
  stream->op = TokenKind::kLtLt;
  stream->lhs = MakeId(f.arena, "byte");
  stream->elements.push_back(MakeId(f.arena, "v"));
  auto result = EvalExpr(stream, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xCDABu);
}

// Req 10: >> ignores slice_size even when width is not divisible by slice_size.
TEST(StreamReordering, RightShiftIgnoresSliceSizeNonDivisible) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [5:0] result;\n"
      "  initial result = {>> 4 {6'b110101}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0b110101u);
}

// Reqs 12, 13: << slices from rightmost bit; last (leftmost) block keeps
// remaining bits without padding or truncation.
// LRM example: { << 4 { 6'b11_0101 }} generates stream 'b0101_11.
TEST(StreamReordering, LeftShiftShortLastBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [5:0] result;\n"
      "  initial result = {<< 4 {6'b110101}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0b010111u);
}

// Req 11: << reverses 16-bit blocks in a 32-bit stream.
TEST(StreamReordering, LeftShift16BitSliceSwap) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  initial result = {<< 16 {32'hABCD1234}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x1234ABCDu);
}

// Edge case: slice_size equals stream width → single block, identity.
TEST(StreamReordering, LeftShiftSliceSizeEqualsWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {<< 8 {8'hAB}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// LRM example: { << 2 { { << { 4'b1101 }} }} generates stream 'b1110.
TEST(StreamReordering, NestedStreamingReordering) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] result;\n"
      "  initial result = {<< 2 { {<< {4'b1101}} }};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0b1110u);
}

}  // namespace
