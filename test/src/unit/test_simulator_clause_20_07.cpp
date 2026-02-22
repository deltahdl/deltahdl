// §20.7: Array query functions

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

struct SysTaskFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr *MkSysCall(Arena &arena, std::string_view name,
                       std::vector<Expr *> args) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kSystemCall;
  e->callee = name;
  e->args = std::move(args);
  return e;
}

static Expr *MkInt(Arena &arena, uint64_t val) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

static Expr *MkId(Arena &arena, std::string_view name) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

namespace {

TEST(SysTask, DimensionsReturnsOne) {
  SysTaskFixture f;
  auto *expr = MkSysCall(f.arena, "$dimensions", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(SysTask, LeftReturnsUpperBound) {
  SysTaskFixture f;
  auto *expr = MkSysCall(f.arena, "$left", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(SysTask, RightReturnsZero) {
  SysTaskFixture f;
  auto *expr = MkSysCall(f.arena, "$right", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, SizeReturnsWidth) {
  SysTaskFixture f;
  auto *expr = MkSysCall(f.arena, "$size", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_GE(result.ToUint64(), 1u);
}

TEST(SysTask, LowReturnsZero) {
  SysTaskFixture f;
  auto *expr = MkSysCall(f.arena, "$low", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, HighReturnsUpperBound) {
  SysTaskFixture f;
  auto *expr = MkSysCall(f.arena, "$high", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_GE(result.ToUint64(), 0u);
}

TEST(SysTask, IncrementReturns) {
  SysTaskFixture f;
  auto *expr = MkSysCall(f.arena, "$increment", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(SysTask, UnpackedDimensionsReturnsZero) {
  SysTaskFixture f;
  auto *expr = MkSysCall(f.arena, "$unpacked_dimensions", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, DimensionsOfUnpackedArray) {
  SysTaskFixture f;
  ArrayInfo info;
  info.lo = 0;
  info.size = 4;
  info.elem_width = 32;
  f.ctx.RegisterArray("arr", info);
  f.ctx.CreateVariable("arr", 32);
  auto *expr = MkSysCall(f.arena, "$dimensions", {MkId(f.arena, "arr")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 2u);
}

TEST(SysTask, UnpackedDimensionsOfArray) {
  SysTaskFixture f;
  ArrayInfo info;
  info.lo = 0;
  info.size = 4;
  info.elem_width = 32;
  f.ctx.RegisterArray("arr", info);
  f.ctx.CreateVariable("arr", 32);
  auto *expr =
      MkSysCall(f.arena, "$unpacked_dimensions", {MkId(f.arena, "arr")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
}

TEST(SysTask, DimensionsOfScalar) {
  SysTaskFixture f;
  f.ctx.CreateVariable("x", 8);
  auto *expr = MkSysCall(f.arena, "$dimensions", {MkId(f.arena, "x")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
}

TEST(SysTask, UnpackedDimensionsOfScalar) {
  SysTaskFixture f;
  f.ctx.CreateVariable("x", 8);
  auto *expr = MkSysCall(f.arena, "$unpacked_dimensions", {MkId(f.arena, "x")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0u);
}

TEST(SysTask, DimensionsOfQueue) {
  SysTaskFixture f;
  f.ctx.CreateQueue("q", 16, -1);
  auto *expr = MkSysCall(f.arena, "$dimensions", {MkId(f.arena, "q")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 2u);
}

TEST(SysTask, UnpackedDimensionsOfQueue) {
  SysTaskFixture f;
  f.ctx.CreateQueue("q", 16, -1);
  auto *expr = MkSysCall(f.arena, "$unpacked_dimensions", {MkId(f.arena, "q")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
}

} // namespace
