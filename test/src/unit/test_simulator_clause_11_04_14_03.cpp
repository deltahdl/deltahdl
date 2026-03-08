#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

// Helper: build a streaming concat expression.
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

// Helper: build a Stmt with streaming concat on LHS.
static Stmt* MakeStreamUnpackAssign(Arena& arena, Expr* lhs_stream, Expr* rhs) {
  auto* s = arena.Create<Stmt>();
  s->kind = StmtKind::kBlockingAssign;
  s->lhs = lhs_stream;
  s->rhs = rhs;
  return s;
}

// §11.4.14.3: Right-shift unpack distributes MSB-first into elements.
TEST(EvalAdv, StreamingUnpackRightShiftBasic) {
  SimFixture f;

  // {>>{ a, b, c }} = 96'b...1  (c gets LSB = 1, a & b get 0)
  MakeVar(f, "a", 32, 0);
  MakeVar(f, "b", 32, 0);
  MakeVar(f, "c", 32, 0);

  auto* lhs = MakeStreamConcat(
      f.arena, TokenKind::kGtGt,
      {MakeId(f.arena, "a"), MakeId(f.arena, "b"), MakeId(f.arena, "c")});
  auto* rhs = MakeInt(f.arena, 1);  // 96-bit value with only LSB set
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 1u);
}

// §11.4.14.3: Right-shift unpack with multi-byte values.
TEST(EvalAdv, StreamingUnpackRightShiftMultiByte) {
  SimFixture f;

  // {>>{ a, b }} = 16'hABCD  → a = 0xAB, b = 0xCD
  MakeVar(f, "a", 8, 0);
  MakeVar(f, "b", 8, 0);

  auto* lhs = MakeStreamConcat(f.arena, TokenKind::kGtGt,
                               {MakeId(f.arena, "a"), MakeId(f.arena, "b")});
  auto* rhs = MakeInt(f.arena, 0xABCD);
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0xABu);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xCDu);
}

// §11.4.14.3: Left-shift unpack reverses slice order before distributing.
TEST(EvalAdv, StreamingUnpackLeftShiftByte) {
  SimFixture f;

  // {<< byte { a, b }} = 16'hABCD
  // Pack analogy: {<< byte {a, b}} would produce {b, a} = 0xCDAB.
  // So unpack: reverse the 8-bit slices of 0xABCD → 0xCDAB, then
  // distribute MSB-first: a = 0xCD, b = 0xAB.
  MakeVar(f, "a", 8, 0);
  MakeVar(f, "b", 8, 0);

  auto* ss = MakeInt(f.arena, 8);
  ss->text = "8";
  auto* lhs =
      MakeStreamConcat(f.arena, TokenKind::kLtLt,
                       {MakeId(f.arena, "a"), MakeId(f.arena, "b")}, ss);
  auto* rhs = MakeInt(f.arena, 0xABCD);
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0xCDu);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xABu);
}

// §11.4.14.3: Source wider than target — extra LSBs truncated.
TEST(EvalAdv, StreamingUnpackSourceWiderTruncatesLSBs) {
  SimFixture f;

  // {>>{ a, b }} = 20'hABCDE → target is 16 bits, consume top 16 bits.
  // Top 16 bits of 20'hABCDE = 0xABCD (bits 19:4), truncate bottom 4.
  // But our RHS is just an integer literal, so we need to handle this
  // via the source width > target width path.
  MakeVar(f, "a2", 8, 0);
  MakeVar(f, "b2", 8, 0);

  auto* lhs = MakeStreamConcat(f.arena, TokenKind::kGtGt,
                               {MakeId(f.arena, "a2"), MakeId(f.arena, "b2")});
  // RHS is wider: 32-bit int with value 0x0000ABCD.
  // Target is 16 bits, consume from MSB of the RHS.
  // With a 32-bit RHS and 16-bit target, top 16 bits = 0x0000.
  // a2 = 0x00, b2 = 0x00... that's not interesting.
  // Let's use 0xABCD0000 to get a2=0xAB, b2=0xCD.
  auto* rhs = MakeInt(f.arena, 0xABCD0000u);
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  // RHS width is 32 (default int), target width is 16.
  // Consume top 16 bits of 0xABCD0000 = 0xABCD.
  EXPECT_EQ(f.ctx.FindVariable("a2")->value.ToUint64(), 0xABu);
  EXPECT_EQ(f.ctx.FindVariable("b2")->value.ToUint64(), 0xCDu);
}

// §11.4.14.3: Right-shift unpack with single element.
TEST(EvalAdv, StreamingUnpackRightShiftSingleElement) {
  SimFixture f;

  MakeVar(f, "x", 16, 0);

  auto* lhs =
      MakeStreamConcat(f.arena, TokenKind::kGtGt, {MakeId(f.arena, "x")});
  auto* rhs = MakeInt(f.arena, 0xBEEF);
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 0xBEEFu);
}

// §11.4.14.3: Left-shift unpack with default slice_size=1 (bit reverse).
TEST(EvalAdv, StreamingUnpackLeftShiftBitReverse) {
  SimFixture f;

  // {<< { v }} = 8'b1010_0101 → bit-reverse → 0b1010_0101 reversed
  // = 0b1010_0101 → reversed = 0b10100101
  // Actually, bit reverse of 0xA5 (10100101) = 10100101 (0xA5). Let me
  // pick a non-palindrome: 0b11001010 = 0xCA → reversed = 0b01010011 = 0x53
  MakeVar(f, "v", 8, 0);

  auto* lhs =
      MakeStreamConcat(f.arena, TokenKind::kLtLt, {MakeId(f.arena, "v")});
  auto* rhs = MakeInt(f.arena, 0xCA);
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("v")->value.ToUint64(), 0x53u);
}

// §11.4.14.3: Left-shift unpack with 4-bit slice size.
TEST(EvalAdv, StreamingUnpackLeftShiftNibbleReverse) {
  SimFixture f;

  // {<< 4 { v }} = 8'hAB → reverse 4-bit nibbles → 0xBA
  MakeVar(f, "v2", 8, 0);

  auto* ss = MakeInt(f.arena, 4);
  ss->text = "4";
  auto* lhs =
      MakeStreamConcat(f.arena, TokenKind::kLtLt, {MakeId(f.arena, "v2")}, ss);
  auto* rhs = MakeInt(f.arena, 0xAB);
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("v2")->value.ToUint64(), 0xBAu);
}

// §11.4.14.3: Left-shift unpack with 16-bit slice, multiple elements.
TEST(EvalAdv, StreamingUnpackLeftShift16BitSlice) {
  SimFixture f;

  // {<< 16 {a, b}} = 32'hDEADBEEF
  // Total target = 32 bits. Reverse 16-bit slices of 0xDEADBEEF:
  // slice0 = 0xBEEF, slice1 = 0xDEAD → reversed = {0xBEEF, 0xDEAD} = 0xBEEFDEAD
  // Distribute MSB-first: a = 0xBEEF, b = 0xDEAD
  MakeVar(f, "a3", 16, 0);
  MakeVar(f, "b3", 16, 0);

  auto* ss = MakeInt(f.arena, 16);
  ss->text = "16";
  auto* lhs =
      MakeStreamConcat(f.arena, TokenKind::kLtLt,
                       {MakeId(f.arena, "a3"), MakeId(f.arena, "b3")}, ss);
  auto* rhs = MakeInt(f.arena, 0xDEADBEEFu);
  auto* stmt = MakeStreamUnpackAssign(f.arena, lhs, rhs);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("a3")->value.ToUint64(), 0xBEEFu);
  EXPECT_EQ(f.ctx.FindVariable("b3")->value.ToUint64(), 0xDEADu);
}

// §11.4.14.3: Unpack round-trips with pack (right-shift).
TEST(EvalAdv, StreamingUnpackRoundTripRightShift) {
  SimFixture f;

  MakeVar(f, "p", 8, 0xAA);
  MakeVar(f, "q", 8, 0xBB);

  // Pack: result = {>> {p, q}} = 0xAABB
  auto* pack = MakeStreamConcat(f.arena, TokenKind::kGtGt,
                                {MakeId(f.arena, "p"), MakeId(f.arena, "q")});
  auto pack_val = EvalExpr(pack, f.ctx, f.arena);
  ASSERT_EQ(pack_val.ToUint64(), 0xAABBu);

  // Unpack into fresh vars: {>> {r, s}} = 0xAABB
  MakeVar(f, "r", 8, 0);
  MakeVar(f, "s", 8, 0);

  auto* unpack = MakeStreamConcat(f.arena, TokenKind::kGtGt,
                                  {MakeId(f.arena, "r"), MakeId(f.arena, "s")});
  auto* rhs_expr = MakeInt(f.arena, pack_val.ToUint64());
  auto* stmt = MakeStreamUnpackAssign(f.arena, unpack, rhs_expr);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 0xAAu);
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 0xBBu);
}

// §11.4.14.3: Unpack round-trips with pack (left-shift).
TEST(EvalAdv, StreamingUnpackRoundTripLeftShift) {
  SimFixture f;

  MakeVar(f, "p2", 8, 0xAA);
  MakeVar(f, "q2", 8, 0xBB);

  // Pack: result = {<< byte {p2, q2}} reverses bytes → 0xBBAA
  auto* ss1 = MakeInt(f.arena, 8);
  ss1->text = "8";
  auto* pack =
      MakeStreamConcat(f.arena, TokenKind::kLtLt,
                       {MakeId(f.arena, "p2"), MakeId(f.arena, "q2")}, ss1);
  auto pack_val = EvalExpr(pack, f.ctx, f.arena);
  ASSERT_EQ(pack_val.ToUint64(), 0xBBAAu);

  // Unpack into fresh vars: {<< byte {r2, s2}} = 0xBBAA → r2=0xAA, s2=0xBB
  MakeVar(f, "r2", 8, 0);
  MakeVar(f, "s2", 8, 0);

  auto* ss2 = MakeInt(f.arena, 8);
  ss2->text = "8";
  auto* unpack =
      MakeStreamConcat(f.arena, TokenKind::kLtLt,
                       {MakeId(f.arena, "r2"), MakeId(f.arena, "s2")}, ss2);
  auto* rhs_expr = MakeInt(f.arena, pack_val.ToUint64());
  auto* stmt = MakeStreamUnpackAssign(f.arena, unpack, rhs_expr);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("r2")->value.ToUint64(), 0xAAu);
  EXPECT_EQ(f.ctx.FindVariable("s2")->value.ToUint64(), 0xBBu);
}

}  // namespace
