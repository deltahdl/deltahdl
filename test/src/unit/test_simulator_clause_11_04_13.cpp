#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_array.h"
#include "helpers_eval_op.h"
#include "helpers_lower_run.h"
#include "helpers_queue.h"
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

// §11.4.13: the set is scanned until a match is found and the operator returns
// 1'b1. Driven through the full pipeline so the left-hand side and the set
// members come from real literals: 5 is a member of {3,5,7}.
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

// §11.4.13: values in the set may be repeated; a match against any occurrence
// still yields 1'b1.
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

// §11.4.13: value ranges in the set may overlap; membership in either range is
// enough for a match.
TEST(EvalOp, InsideOverlappingRangesMatch) {
  SimFixture f;
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 7);
  inside->elements.push_back(
      MakeRange(f.arena, MakeInt(f.arena, 5), MakeInt(f.arena, 10)));
  inside->elements.push_back(
      MakeRange(f.arena, MakeInt(f.arena, 3), MakeInt(f.arena, 8)));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §11.4.13: the result is the OR reduction of the per-member comparisons, so a
// definite match anywhere in the set produces 1'b1 even when another member's
// comparison is ambiguous (x). Here `om` has an x bit that makes the first
// comparison ambiguous, but the [0:15] range is a definite match.
TEST(EvalOpXZ, InsideOrReductionMatchOverridesAmbiguous) {
  SimFixture f;

  MakeVar4(f, "om", 4, 0b0000, 0b0100);

  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "om");

  inside->elements.push_back(MakeInt(f.arena, 0b0100));

  inside->elements.push_back(
      MakeRange(f.arena, MakeInt(f.arena, 0), MakeInt(f.arena, 15)));

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §11.4.13: the marquee do-not-care example driven through the full pipeline.
// With `3'bz11 inside {3'b1?1, 3'b011}` the z bit on the left-hand side is NOT
// treated as a do-not-care (unlike the `?` wildcard on the set side), so every
// comparison is ambiguous and none matches; the result is a definite x, the OR
// reduction of the per-member comparisons. A definite 0/1 would clear bval, so
// observing bval set proves the x result rather than a match or a miss.
TEST(ExpressionSim, InsideResultXWhenLhsHasZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic r;\n"
      "  initial r = 3'bz11 inside {3'b1?1, 3'b011};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval & 1u, 0u);
}

// §11.4.13: absolute-tolerance range [A +/- B] designates [A-B : A+B]. Driven
// end to end so the `+/-` token, not a hand-built AST, produces the bounds:
// [7 +/- 5] = [2:12]; 10 is inside (match), 20 is outside (miss).
TEST(ExpressionSim, InsideAbsoluteToleranceFullPipeline) {
  SimFixture f;
  auto [hit, miss] =
      RunModuleTwoVars(f,
                       "module t;\n"
                       "  logic hit, miss;\n"
                       "  initial begin\n"
                       "    hit = 8'd10 inside {[8'd7 +/- 8'd5]};\n"
                       "    miss = 8'd20 inside {[8'd7 +/- 8'd5]};\n"
                       "  end\n"
                       "endmodule\n",
                       "hit", "miss");
  EXPECT_EQ(hit, 1u);
  EXPECT_EQ(miss, 0u);
}

// §11.4.13: relative-tolerance range [A +%- B] designates a tolerance of
// A*B/100 with truncation (not rounding) on the real-to-integral conversion.
// [7 +%- 25] has tolerance trunc(1.75) = 1, so the range is [6:8]: 6 matches
// (truncation kept the low bound reachable) while 5 misses.
TEST(ExpressionSim, InsideRelativeToleranceTruncatesFullPipeline) {
  SimFixture f;
  auto [hit, miss] =
      RunModuleTwoVars(f,
                       "module t;\n"
                       "  logic hit, miss;\n"
                       "  initial begin\n"
                       "    hit = 8'd6 inside {[8'd7 +%- 8'd25]};\n"
                       "    miss = 8'd5 inside {[8'd7 +%- 8'd25]};\n"
                       "  end\n"
                       "endmodule\n",
                       "hit", "miss");
  EXPECT_EQ(hit, 1u);
  EXPECT_EQ(miss, 0u);
}

// §11.4.13: a $ bound denotes the lowest or highest value of the left-hand
// side's type. Driven end to end so the `$` token resolves against the operand
// width: [100:$] resolves the upper bound to 255 for an 8-bit value (250 is a
// match), while [$:100] resolves the lower bound to 0 (150 exceeds 100, a miss)
// — proving the open bound is the type extreme, not an unbounded range. The
// miss also covers an in-order, non-empty range whose value lies above the
// high bound.
TEST(ExpressionSim, InsideDollarBoundsFullPipeline) {
  SimFixture f;
  auto [hi, lo] = RunModuleTwoVars(f,
                                   "module t;\n"
                                   "  logic hi, lo;\n"
                                   "  initial begin\n"
                                   "    hi = 8'd250 inside {[8'd100:$]};\n"
                                   "    lo = 8'd150 inside {[$:8'd100]};\n"
                                   "  end\n"
                                   "endmodule\n",
                                   "hi", "lo");
  EXPECT_EQ(hi, 1u);
  EXPECT_EQ(lo, 0u);
}

// §11.4.13: when the bound left of the colon exceeds the bound to its right the
// range is empty and contains no values, so the membership test is a miss even
// for a value that lies numerically between the two bounds.
TEST(ExpressionSim, InsideInvertedRangeEmptyFullPipeline) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  logic r;\n"
                         "  initial r = 8'd5 inside {[8'd10:8'd3]};\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 0u);
}

// §11.4.13: a set member naming an unpacked array is traversed down to its
// singular elements, so {5, arr} with arr = '{10,20,30} behaves like
// {5,10,20,30}. Builds `ex inside {1, 2, q}` for a 32-bit `ex` holding `ex_val`
// and returns the evaluated match result; q is '{3,4,5}. The queue exercises
// the dynamically-sized-array descent branch (a distinct container from the
// fixed-array case below).
static uint64_t EvalInsideQueueMember(SimFixture& f, uint64_t ex_val) {
  MakeQueue(f, "q", {3, 4, 5});
  auto* var = f.ctx.CreateVariable("ex", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, ex_val);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "ex");
  inside->elements.push_back(MakeInt(f.arena, 1));
  inside->elements.push_back(MakeInt(f.arena, 2));
  inside->elements.push_back(MakeId(f.arena, "q"));
  return EvalExpr(inside, f.ctx, f.arena).ToUint64();
}

TEST(EvalOp, InsideQueueMemberDescends) {
  SimFixture f;
  EXPECT_EQ(EvalInsideQueueMember(f, 4), 1u);
}

TEST(EvalOp, InsideQueueMemberNoMatch) {
  SimFixture f;
  EXPECT_EQ(EvalInsideQueueMember(f, 9), 0u);
}

// §11.4.13: the same descent for a fixed-size unpacked array, driven through
// the full pipeline from a real array declaration + assignment-pattern
// initializer (rather than a stubbed ArrayInfo): arr holds {10,20,30}, so 20
// matches by descent while 7 misses — the constant 5 alone supplies neither.
TEST(ExpressionSim, InsideUnpackedArrayMemberDescendsFullPipeline) {
  SimFixture f;
  auto [hit, miss] =
      RunModuleTwoVars(f,
                       "module t;\n"
                       "  logic [7:0] arr [0:2] = '{8'd10, 8'd20, 8'd30};\n"
                       "  logic hit, miss;\n"
                       "  initial begin\n"
                       "    hit = 8'd20 inside {8'd5, arr};\n"
                       "    miss = 8'd7 inside {8'd5, arr};\n"
                       "  end\n"
                       "endmodule\n",
                       "hit", "miss");
  EXPECT_EQ(hit, 1u);
  EXPECT_EQ(miss, 0u);
}

// §11.4.13: descent into an unpacked-array set member continues until a
// singular value is reached, so a MULTIDIMENSIONAL array contributes each of
// its leaf elements. Built from a real 2-D array whose leaves are populated by
// compound-select procedural writes (§7.4.2) and driven end to end: grid holds
// {{10,20},{30,40}}, so 30 (a leaf, reachable only by descending both
// dimensions) matches while 7 misses. The constant 5 supplies neither.
TEST(ExpressionSim, InsideMultiDimArrayMemberDescendsFullPipeline) {
  SimFixture f;
  auto [hit, miss] =
      RunModuleTwoVars(f,
                       "module t;\n"
                       "  logic [7:0] grid [0:1][0:1];\n"
                       "  logic hit, miss;\n"
                       "  initial begin\n"
                       "    grid[0][0] = 8'd10; grid[0][1] = 8'd20;\n"
                       "    grid[1][0] = 8'd30; grid[1][1] = 8'd40;\n"
                       "    hit = 8'd30 inside {8'd5, grid};\n"
                       "    miss = 8'd7 inside {8'd5, grid};\n"
                       "  end\n"
                       "endmodule\n",
                       "hit", "miss");
  EXPECT_EQ(hit, 1u);
  EXPECT_EQ(miss, 0u);
}

// §11.4.13: the left-hand side and the set members may all be runtime
// variables (the operator's headline form, `a inside {b, c}`), so the members'
// values come from variable reads rather than literals. With a=5, b=3, c=5 the
// value 5 matches the second member.
TEST(ExpressionSim, InsideValueMembersFromVariables) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  logic [7:0] a, b, c;\n"
                         "  logic r;\n"
                         "  initial begin\n"
                         "    a = 8'd5; b = 8'd3; c = 8'd5;\n"
                         "    r = a inside {b, c};\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 1u);
}

// §11.4.13: a set member is an expression, so its value may be supplied by a
// parameter constant rather than a literal (a distinct constant-evaluation
// path). `8'd5 inside {P}` with P = 8'd5 matches.
TEST(ExpressionSim, InsideValueMemberFromParameter) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  parameter P = 8'd5;\n"
                         "  logic r;\n"
                         "  initial r = 8'd5 inside {P};\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 1u);
}

// §11.4.13: the same, with the set member supplied by a localparam constant
// (a separate constant form from a module parameter).
TEST(ExpressionSim, InsideValueMemberFromLocalparam) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  localparam P = 8'd5;\n"
                         "  logic r;\n"
                         "  initial r = 8'd5 inside {P};\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 1u);
}

// §11.4.13: a range's low and high bounds are expressions and may be supplied
// by parameter constants. [LO:HI] = [5:10]: 7 is inside (match), 20 is outside
// (miss), exercising the relational membership test over parameter-valued
// bounds.
TEST(ExpressionSim, InsideRangeBoundsFromParameters) {
  SimFixture f;
  auto [hit, miss] = RunModuleTwoVars(f,
                                      "module t;\n"
                                      "  parameter LO = 8'd5;\n"
                                      "  parameter HI = 8'd10;\n"
                                      "  logic hit, miss;\n"
                                      "  initial begin\n"
                                      "    hit = 8'd7 inside {[LO:HI]};\n"
                                      "    miss = 8'd20 inside {[LO:HI]};\n"
                                      "  end\n"
                                      "endmodule\n",
                                      "hit", "miss");
  EXPECT_EQ(hit, 1u);
  EXPECT_EQ(miss, 0u);
}

// §11.4.13: range bounds supplied by localparam constants take the same path.
TEST(ExpressionSim, InsideRangeBoundsFromLocalparams) {
  SimFixture f;
  auto [hit, miss] = RunModuleTwoVars(f,
                                      "module t;\n"
                                      "  localparam LO = 8'd5;\n"
                                      "  localparam HI = 8'd10;\n"
                                      "  logic hit, miss;\n"
                                      "  initial begin\n"
                                      "    hit = 8'd7 inside {[LO:HI]};\n"
                                      "    miss = 8'd20 inside {[LO:HI]};\n"
                                      "  end\n"
                                      "endmodule\n",
                                      "hit", "miss");
  EXPECT_EQ(hit, 1u);
  EXPECT_EQ(miss, 0u);
}

// §11.4.13: the left-hand side is any singular expression, including one whose
// value is a parameter constant. `P inside {3,5,7}` with P = 8'd5 matches.
TEST(ExpressionSim, InsideLhsFromParameter) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  parameter P = 8'd5;\n"
                         "  logic r;\n"
                         "  initial r = P inside {8'd3, 8'd5, 8'd7};\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 1u);
}

}  // namespace
