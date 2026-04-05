#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
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

// Wildcard equality: x/z in RHS set value acts as don't-care.
// 4'b0101 should match 4'b01x1 (x bit in RHS is wildcard).
TEST(EvalOpXZ, InsideRhsXActsAsDontCare) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("wv", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0b0101);

  // Build a set element with x bits: aval=0b0001, bval=0b0010 → 4'b00x1.
  auto* xval = f.arena.Create<Expr>();
  xval->kind = ExprKind::kIdentifier;
  xval->text = "xv";
  auto* xvar = f.ctx.CreateVariable("xv", 4);
  xvar->value = MakeLogic4Vec(f.arena, 4);
  xvar->value.words[0].aval = 0b0001;
  xvar->value.words[0].bval = 0b0110;  // bits 1,2 are x → 4'b0xx1

  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "wv");
  inside->elements.push_back(xval);

  auto result = EvalExpr(inside, f.ctx, f.arena);
  // With wildcard equality, 4'b0101 ==? 4'b0xx1 should be 1.
  EXPECT_EQ(result.ToUint64(), 1u);
}

// LHS x/z bits are NOT treated as don't-care.
// 4'b0x01 inside {4'b0101} → x (ambiguous), not 1.
TEST(EvalOpXZ, InsideLhsXNotDontCare) {
  SimFixture f;

  // LHS: 4'b0x01 (aval=0b0001, bval=0b0100).
  MakeVar4(f, "lx", 4, 0b0001, 0b0100);

  // RHS: plain 4'b0101.
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "lx");
  inside->elements.push_back(MakeInt(f.arena, 0b0101));

  auto result = EvalExpr(inside, f.ctx, f.arena);
  // LHS has x in a position where RHS has 1 → ambiguous (x), not a match.
  EXPECT_NE(result.words[0].bval, 0u);
}

// Range boundaries are inclusive: lo and hi themselves match.
TEST(EvalOp, InsideRangeLoBoundaryInclusive) {
  SimFixture f;
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 3);
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 3),
                                       MakeInt(f.arena, 7)));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, InsideRangeHiBoundaryInclusive) {
  SimFixture f;
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 7);
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 3),
                                       MakeInt(f.arena, 7)));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// Inverted range [10:3] should be empty — no values match.
TEST(EvalOp, InsideInvertedRangeIsEmpty) {
  SimFixture f;
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 5);
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 10),
                                       MakeInt(f.arena, 3)));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// Repeated values in set: value appears twice, still matches.
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

// Overlapping ranges: value in both ranges still matches.
TEST(EvalOp, InsideOverlappingRangesMatch) {
  SimFixture f;
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 7);
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 5),
                                       MakeInt(f.arena, 10)));
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 3),
                                       MakeInt(f.arena, 8)));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// OR-reduction: some comparisons yield x, none yield 1 → result is x.
TEST(EvalOpXZ, InsideOrReductionAmbiguous) {
  SimFixture f;

  // LHS: 4'b0x00 (aval=0b0000, bval=0b0100).
  MakeVar4(f, "ov", 4, 0b0000, 0b0100);

  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "ov");
  // 4'b0100 — may or may not match depending on x bit.
  inside->elements.push_back(MakeInt(f.arena, 0b0100));
  // 4'b1111 — clearly doesn't match regardless of x bit.
  inside->elements.push_back(MakeInt(f.arena, 0b1111));

  auto result = EvalExpr(inside, f.ctx, f.arena);
  // At least one comparison is ambiguous, none is definite match → x.
  EXPECT_NE(result.words[0].bval, 0u);
}

// OR-reduction: one comparison is x but another is definite match → 1.
TEST(EvalOpXZ, InsideOrReductionMatchOverridesAmbiguous) {
  SimFixture f;

  // LHS: 4'b0x00 (aval=0b0000, bval=0b0100).
  MakeVar4(f, "om", 4, 0b0000, 0b0100);

  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "om");
  // 4'b0100 — ambiguous due to x in LHS.
  inside->elements.push_back(MakeInt(f.arena, 0b0100));
  // Range [0:15] — covers all 4-bit values, definite match.
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 0),
                                       MakeInt(f.arena, 15)));

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// Relative tolerance truncation: 25% of 7 should truncate to 1, not round to 2.
// So [7 +%- 25] → [7-1 : 7+1] = [6:8].
TEST(EvalAdv, InsideRelToleranceTruncation) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("tt", 8);
  // Value 6 should be at the lower boundary [6:8].
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

// Value 5 is below the truncated range [6:8] so should NOT match.
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

}  // namespace
