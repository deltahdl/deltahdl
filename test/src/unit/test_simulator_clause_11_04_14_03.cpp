#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

static Expr* MakeStreamConcat(Arena& arena, TokenKind dir,
                              std::vector<Expr*> elems,
                              Expr* slice_size = nullptr) {
  auto* sc = arena.Create<Expr>();
  sc->kind = ExprKind::kStreamingConcat;
  sc->op = dir;
  sc->lhs = slice_size;
  sc->elements = std::move(elems);
  return sc;
}

static Stmt* MakeStreamUnpackAssign(Arena& arena, Expr* lhs_stream, Expr* rhs) {
  auto* s = arena.Create<Stmt>();
  s->kind = StmtKind::kBlockingAssign;
  s->lhs = lhs_stream;
  s->rhs = rhs;
  return s;
}

TEST(StreamingUnpack, StreamingUnpackRightShiftBasic) {
  SimFixture f;

  MakeVar(f, "a", 32, 0);
  MakeVar(f, "b", 32, 0);
  MakeVar(f, "c", 32, 0);

  auto* lhs = MakeStreamConcat(
      f.arena, TokenKind::kGtGt,
      {MakeId(f.arena, "a"), MakeId(f.arena, "b"), MakeId(f.arena, "c")});
  auto* rhs = MakeInt(f.arena, 1);
  rhs->text = "96'h0";
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 1u);
}

TEST(StreamingUnpack, StreamingUnpackRightShiftMultiByte) {
  SimFixture f;

  MakeVar(f, "a", 8, 0);
  MakeVar(f, "b", 8, 0);

  auto* lhs = MakeStreamConcat(f.arena, TokenKind::kGtGt,
                               {MakeId(f.arena, "a"), MakeId(f.arena, "b")});
  auto* rhs = MakeInt(f.arena, 0xABCD);
  rhs->text = "16'h0";
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0xABu);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xCDu);
}

TEST(StreamingUnpack, StreamingUnpackLeftShiftByte) {
  SimFixture f;

  MakeVar(f, "a", 8, 0);
  MakeVar(f, "b", 8, 0);

  auto* ss = MakeInt(f.arena, 8);
  ss->text = "8";
  auto* lhs =
      MakeStreamConcat(f.arena, TokenKind::kLtLt,
                       {MakeId(f.arena, "a"), MakeId(f.arena, "b")}, ss);
  auto* rhs = MakeInt(f.arena, 0xABCD);
  rhs->text = "16'h0";
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0xCDu);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xABu);
}

TEST(StreamingUnpack, StreamingUnpackSourceWiderTruncatesLSBs) {
  SimFixture f;

  MakeVar(f, "a2", 8, 0);
  MakeVar(f, "b2", 8, 0);

  auto* lhs = MakeStreamConcat(f.arena, TokenKind::kGtGt,
                               {MakeId(f.arena, "a2"), MakeId(f.arena, "b2")});

  auto* rhs = MakeInt(f.arena, 0xABCD0000u);
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("a2")->value.ToUint64(), 0xABu);
  EXPECT_EQ(f.ctx.FindVariable("b2")->value.ToUint64(), 0xCDu);
}

TEST(StreamingUnpack, StreamingUnpackRightShiftSingleElement) {
  SimFixture f;

  MakeVar(f, "x", 16, 0);

  auto* lhs =
      MakeStreamConcat(f.arena, TokenKind::kGtGt, {MakeId(f.arena, "x")});
  auto* rhs = MakeInt(f.arena, 0xBEEF);
  rhs->text = "16'h0";
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 0xBEEFu);
}

TEST(StreamingUnpack, StreamingUnpackLeftShiftBitReverse) {
  SimFixture f;

  MakeVar(f, "v", 8, 0);

  auto* lhs =
      MakeStreamConcat(f.arena, TokenKind::kLtLt, {MakeId(f.arena, "v")});
  auto* rhs = MakeInt(f.arena, 0xCA);
  rhs->text = "8'h0";
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("v")->value.ToUint64(), 0x53u);
}

TEST(StreamingUnpack, StreamingUnpackLeftShiftNibbleReverse) {
  SimFixture f;

  MakeVar(f, "v2", 8, 0);

  auto* ss = MakeInt(f.arena, 4);
  ss->text = "4";
  auto* lhs =
      MakeStreamConcat(f.arena, TokenKind::kLtLt, {MakeId(f.arena, "v2")}, ss);
  auto* rhs = MakeInt(f.arena, 0xAB);
  rhs->text = "8'h0";
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("v2")->value.ToUint64(), 0xBAu);
}

TEST(StreamingUnpack, StreamingUnpackLeftShift16BitSlice) {
  SimFixture f;

  MakeVar(f, "a3", 16, 0);
  MakeVar(f, "b3", 16, 0);

  auto* ss = MakeInt(f.arena, 16);
  ss->text = "16";
  auto* lhs =
      MakeStreamConcat(f.arena, TokenKind::kLtLt,
                       {MakeId(f.arena, "a3"), MakeId(f.arena, "b3")}, ss);
  auto* rhs = MakeInt(f.arena, 0xDEADBEEFu);
  rhs->text = "32'h0";
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("a3")->value.ToUint64(), 0xBEEFu);
  EXPECT_EQ(f.ctx.FindVariable("b3")->value.ToUint64(), 0xDEADu);
}

TEST(StreamingUnpack, StreamingUnpackRoundTripRightShift) {
  SimFixture f;

  MakeVar(f, "p", 8, 0xAA);
  MakeVar(f, "q", 8, 0xBB);

  auto* pack = MakeStreamConcat(f.arena, TokenKind::kGtGt,
                                {MakeId(f.arena, "p"), MakeId(f.arena, "q")});
  auto pack_val = EvalExpr(pack, f.ctx, f.arena);
  ASSERT_EQ(pack_val.ToUint64(), 0xAABBu);

  MakeVar(f, "r", 8, 0);
  MakeVar(f, "s", 8, 0);

  auto* unpack = MakeStreamConcat(f.arena, TokenKind::kGtGt,
                                  {MakeId(f.arena, "r"), MakeId(f.arena, "s")});
  auto* rhs_expr = MakeInt(f.arena, pack_val.ToUint64());
  rhs_expr->text = "16'h0";
  auto* stmt = MakeStreamUnpackAssign(f.arena, unpack, rhs_expr);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 0xAAu);
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 0xBBu);
}

TEST(StreamingUnpack, StreamingUnpackRoundTripLeftShift) {
  SimFixture f;

  MakeVar(f, "p2", 8, 0xAA);
  MakeVar(f, "q2", 8, 0xBB);

  auto* ss1 = MakeInt(f.arena, 8);
  ss1->text = "8";
  auto* pack =
      MakeStreamConcat(f.arena, TokenKind::kLtLt,
                       {MakeId(f.arena, "p2"), MakeId(f.arena, "q2")}, ss1);
  auto pack_val = EvalExpr(pack, f.ctx, f.arena);
  ASSERT_EQ(pack_val.ToUint64(), 0xBBAAu);

  MakeVar(f, "r2", 8, 0);
  MakeVar(f, "s2", 8, 0);

  auto* ss2 = MakeInt(f.arena, 8);
  ss2->text = "8";
  auto* unpack =
      MakeStreamConcat(f.arena, TokenKind::kLtLt,
                       {MakeId(f.arena, "r2"), MakeId(f.arena, "s2")}, ss2);
  auto* rhs_expr = MakeInt(f.arena, pack_val.ToUint64());
  rhs_expr->text = "16'h0";
  auto* stmt = MakeStreamUnpackAssign(f.arena, unpack, rhs_expr);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("r2")->value.ToUint64(), 0xAAu);
  EXPECT_EQ(f.ctx.FindVariable("s2")->value.ToUint64(), 0xBBu);
}

TEST(StreamingUnpack, SourceExactlyMatchesTargetWidth) {
  SimFixture f;

  MakeVar(f, "a", 8, 0);
  MakeVar(f, "b", 8, 0);
  MakeVar(f, "c", 8, 0);
  MakeVar(f, "d", 8, 0);

  auto* lhs = MakeStreamConcat(
      f.arena, TokenKind::kGtGt,
      {MakeId(f.arena, "a"), MakeId(f.arena, "b"), MakeId(f.arena, "c"),
       MakeId(f.arena, "d")});
  auto* rhs = MakeInt(f.arena, 0xDEADBEEFu);
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0xDEu);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xADu);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 0xBEu);
  EXPECT_EQ(f.ctx.FindVariable("d")->value.ToUint64(), 0xEFu);
}

TEST(StreamingUnpack, SourceNarrowerThanTargetErrors) {
  SimFixture f;

  MakeVar(f, "a", 32, 0);
  MakeVar(f, "b", 32, 0);
  MakeVar(f, "c", 32, 0);

  auto* lhs = MakeStreamConcat(
      f.arena, TokenKind::kGtGt,
      {MakeId(f.arena, "a"), MakeId(f.arena, "b"), MakeId(f.arena, "c")});
  auto* rhs = MakeInt(f.arena, 0xABCD);
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StreamingUnpack, SourceWiderConsumesMsbWithMixedWidths) {
  SimFixture f;

  MakeVar(f, "a", 16, 0);
  MakeVar(f, "b", 8, 0);

  auto* lhs = MakeStreamConcat(f.arena, TokenKind::kGtGt,
                               {MakeId(f.arena, "a"), MakeId(f.arena, "b")});
  auto* rhs = MakeInt(f.arena, 0xABCDEF12u);
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0xABCDu);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xEFu);
}

}  // namespace
