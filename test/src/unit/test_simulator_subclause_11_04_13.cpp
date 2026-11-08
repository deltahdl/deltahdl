#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "helpers_queue.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
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

TEST(ExpressionSim, InsideValueMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = 8'd5 inside {8'd3, 8'd5, 8'd7};\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

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

TEST(EvalOpXZ, InsideOrReductionMatchOverridesAmbiguous) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [3:0] om = 4'b0x00;\n"
                       "  initial $display(\"%b %b %b\",\n"
                       "      om inside {4'b0100, [4:4], 4'b0?00},\n"
                       "      om inside {[4:4]}, om inside {4'b1000});\n"
                       "endmodule\n",
                       f),
            "1 x 0\n");
}

TEST(ExpressionSim, InsideResultXWhenLhsHasZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic r;\n"
      "  initial r = 3'bz11 inside {3'b1?1, 3'b011};\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval & 1u, 0u);
}

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

TEST(InsideOperatorSim, AnAssociativeArrayInTheSetContributesItsValues) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int m[string]; int mi[int];\n"
      "  initial begin\n"
      "    m[\"a\"] = 3; m[\"b\"] = 9; mi[5] = 7;\n"
      "    $display(\"%0d %0d %0d %0d\", 3 inside {m}, 4 inside {m},\n"
      "             7 inside {mi, 1}, 5 inside {mi});\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0 1 0\n");
}

TEST(InsideOperatorSim, MembersAndRangesCompareOnTheOperandsTypes) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  int x = -3;\n"
                 "  real r = 1.0;\n"
                 "  logic signed [3:0] a = -1;\n"
                 "  logic [127:0] w = 0;\n"
                 "  string s = \"b\";\n"
                 "  initial $display(\"%b %b %b %b %b %b\",\n"
                 "      x inside {[-5:5]}, r inside {1}, a inside {-1},\n"
                 "      w inside {{1'b1, 64'h0}}, s inside {[\"a\":\"c\"]},\n"
                 "      x inside {[5:-5]});\n"
                 "endmodule\n",
                 f),
      "1 1 1 0 1 0\n");
}

TEST(InsideOperatorSim, DollarBoundIsTheLeftOperandsTypeExtreme) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int x = -5;\n"
                       "  logic [3:0] u = 9;\n"
                       "  real r = -1.0e300;\n"
                       "  initial $display(\"%b %b %b %b %b\",\n"
                       "      x inside {[$:0]}, x inside {[0:$]},\n"
                       "      u inside {[10:$]}, u inside {[$:9]},\n"
                       "      r inside {[$:0.0]});\n"
                       "endmodule\n",
                       f),
            "1 0 0 1 1\n");
}

TEST(InsideOperatorSim, ToleranceRangeTakesTheTypeOfItsCentre) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  real r = 8.5;\n"
                 "  int A = -7, v = -100, w = -8, z = -5;\n"
                 "  logic [3:0] b = 4'bx001;\n"
                 "  initial $display(\"%b %b %b %b %b %b\",\n"
                 "      r inside {[7.0 +%- 25]}, r inside {[7.0 +/- 1.5]},\n"
                 "      v inside {[A +%- 25]}, w inside {[A +%- 25]},\n"
                 "      z inside {[A +%- 25]}, 1 inside {[b +/- 1]});\n"
                 "endmodule\n",
                 f),
      "1 1 0 1 0 x\n");
}

}  // namespace
