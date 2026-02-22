// §11.4.14: Streaming operators (pack/unpack)

#include <gtest/gtest.h>
#include <cstring>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"  // StructTypeInfo, StructFieldInfo

using namespace delta;

// Shared fixture for advanced expression evaluation tests (§11 phases 22+).
struct EvalAdvFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr* MakeId(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

static Variable* MakeVar(EvalAdvFixture& f, std::string_view name,
                         uint32_t width, uint64_t val) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4VecVal(f.arena, width, val);
  return var;
}

namespace {

// ==========================================================================
// §11.4.14: Streaming operator — basic integral test (existing behavior)
// ==========================================================================
TEST(EvalAdv, StreamingLeftShiftReversesSlices) {
  EvalAdvFixture f;
  // {<< 8 {16'hABCD}} → reverse 8-bit slices: 0xCDAB
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
  EvalAdvFixture f;
  // {>> 8 {16'hABCD}} → no reversal, same as concat.
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

// ==========================================================================
// §11.4.14.1: Streaming with unpacked array — element concatenation
// ==========================================================================
TEST(EvalAdv, StreamingUnpackedArrayConcat) {
  EvalAdvFixture f;
  // Create unpacked array: arr[0]=0xAB, arr[1]=0xCD, each 8-bit.
  MakeVar(f, "arr[0]", 8, 0xAB);
  MakeVar(f, "arr[1]", 8, 0xCD);
  ArrayInfo info{};
  info.lo = 0;
  info.size = 2;
  info.elem_width = 8;
  f.ctx.RegisterArray("arr", info);

  // {>> {arr}} → right-shift stream: concatenate MSB-first = 0xABCD.
  auto* stream = f.arena.Create<Expr>();
  stream->kind = ExprKind::kStreamingConcat;
  stream->op = TokenKind::kGtGt;
  stream->elements.push_back(MakeId(f.arena, "arr"));
  auto result = EvalExpr(stream, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0xABCDu);
}

TEST(EvalAdv, StreamingUnpackedArrayLeftShift) {
  EvalAdvFixture f;
  // Create unpacked array: arr2[0]=0xAB, arr2[1]=0xCD.
  MakeVar(f, "arr2[0]", 8, 0xAB);
  MakeVar(f, "arr2[1]", 8, 0xCD);
  ArrayInfo info{};
  info.lo = 0;
  info.size = 2;
  info.elem_width = 8;
  f.ctx.RegisterArray("arr2", info);

  // {<< 8 {arr2}} → left-shift stream with 8-bit slices: reversal = 0xCDAB.
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
  EvalAdvFixture f;
  // Array with 3 elements but only [0] and [2] exist — [1] should be X.
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
  // arr3[0]=0x11, arr3[1]=X(0x00), arr3[2]=0x33 → 0x110033
  EXPECT_EQ(result.ToUint64(), 0x110033u);
}

}  // namespace
