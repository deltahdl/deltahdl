#include <gtest/gtest.h>

#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_sequence_ticks.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine_queues.h"
#include "simulator/sva_engine_sequences.h"

using namespace delta;

struct SvaFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

namespace {

TEST(SvaEngine, IntersectRequiresBothOperandsToMatch) {
  EXPECT_TRUE(EvalSequenceIntersect(true, true, 5, 5));

  EXPECT_FALSE(EvalSequenceIntersect(true, false, 5, 5));
  EXPECT_FALSE(EvalSequenceIntersect(false, true, 5, 5));
  EXPECT_FALSE(EvalSequenceIntersect(false, false, 5, 5));
}

TEST(SvaEngine, IntersectRequiresEqualMatchLengths) {
  EXPECT_TRUE(EvalSequenceAnd(true, true));
  EXPECT_FALSE(EvalSequenceIntersect(true, true, 4, 6));
  EXPECT_FALSE(EvalSequenceIntersect(true, true, 6, 4));

  EXPECT_TRUE(EvalSequenceIntersect(true, true, 1, 1));
}

TEST(SvaEngine, IntersectPairsEqualLengthOperandMatches) {
  std::vector<IntersectOperandMatch> a = {
      {1, 9}, {2, 10}, {3, 11}, {4, 12}, {5, 13}};
  std::vector<IntersectOperandMatch> b = {{5, 13}};

  auto matches = EvalSequenceIntersectMatches(a, b);

  ASSERT_EQ(matches.size(), 1u);
  EXPECT_EQ(matches[0].length, 5u);
  EXPECT_EQ(matches[0].match_point, 13u);
}

TEST(SvaEngine, IntersectYieldsOneCompositeMatchPerEqualLengthPair) {
  std::vector<IntersectOperandMatch> a = {{2, 5}, {3, 6}};
  std::vector<IntersectOperandMatch> b = {{2, 5}, {3, 6}, {4, 7}};

  auto matches = EvalSequenceIntersectMatches(a, b);

  ASSERT_EQ(matches.size(), 2u);
  EXPECT_EQ(matches[0].length, 2u);
  EXPECT_EQ(matches[0].match_point, 5u);
  EXPECT_EQ(matches[1].length, 3u);
  EXPECT_EQ(matches[1].match_point, 6u);
}

TEST(SvaEngine, IntersectHasNoMatchWithoutAnEqualLengthPair) {
  std::vector<IntersectOperandMatch> a = {{2, 5}, {3, 6}};
  std::vector<IntersectOperandMatch> b = {{4, 7}, {5, 8}};

  EXPECT_TRUE(EvalSequenceIntersectMatches(a, b).empty());

  EXPECT_TRUE(EvalSequenceIntersectMatches(a, {}).empty());
  EXPECT_TRUE(EvalSequenceIntersectMatches({}, b).empty());
}

TEST(SequenceIntersect, PairsTheOperandMatchesOfTheSameLength) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource(
          "(te1 ##[1:5] te2) intersect (te3 ##2 te4 ##2 te5)",
          DriveTicks(
              {{1, 2, 8}, {9, 10, 11, 12, 13}, {2, 3, 8}, {4, 10}, {6, 12}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 115u);
}

TEST(SequenceIntersect, OperandMatchesOfDifferentLengthsDoNotPair) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource(
          "(te1 ##[1:5] te2) intersect (te3 ##2 te4 ##2 te5)",
          DriveTicks({{1, 2, 8}, {10}, {2, 3, 8}, {4, 10}, {6, 12}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 0u);
}

TEST(SequenceIntersect, EachPairOfTheSameLengthIsAMatch) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource(
          "(te1 ##[1:5] te2) intersect (te3 ##2 te4 ##[0:2] te5)",
          DriveTicks({{1, 2, 8}, {10, 12}, {2, 3, 8}, {4, 10}, {6, 10, 12}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 115u);
}

TEST(SequenceIntersect, BindsTighterThanAnd) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource(
          "te1 ##2 te2 intersect te3 ##2 te4 and te3 ##2 te4 ##2 te5",
          DriveTicks({{1, 2, 8}, {10, 12}, {2, 3, 8}, {4, 10}, {6, 12}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 115u);
}

TEST(SequenceIntersect, AGroupIsOneOperandOfTheChainAroundIt) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource(
          "te1 ##1 (te2[*1:2] intersect te3 ##1 te4) ##1 te5",
          DriveTicks({{2, 7}, {3, 4, 8}, {3, 8}, {4, 9}, {5, 10}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 45u);
}

TEST(SequenceIntersect, AnInstanceIsOneOperandOfTheChainAroundIt) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource(
          "te1 ##1 both ##1 te5",
          DriveTicks({{2, 7}, {3, 4, 8}, {3, 8}, {4, 9}, {5, 10}}),
          "  sequence both;\n"
          "    te2[*1:2] intersect te3 ##1 te4;\n"
          "  endsequence\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 45u);
}

TEST(SequenceIntersect, AGroupIsAnImplicationsConsequentOrAntecedent) {
  SimFixture f;
  auto* p1 = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] sv = 10'b0100010000, ev = 10'b0111011000,\n"
      "            gv = 10'b0001000100;\n"
      "  bit s, e, g;\n"
      "  assign s = sv[0]; assign e = ev[0]; assign g = gv[0];\n"
      "  always @(negedge clk) begin\n"
      "    sv <= sv << 1; ev <= ev << 1; gv <= gv << 1;\n"
      "  end\n"
      "  int p1 = 0, f1 = 0, p2 = 0, f2 = 0;\n"
      "  assert property (@(posedge clk) s |-> (e[*3] intersect ##2 g))\n"
      "    p1++; else f1++;\n"
      "  assert property (@(posedge clk)\n"
      "    (s ##0 (e[*3] intersect ##2 g)) |=> e) p2++; else f2++;\n"
      "endmodule\n",
      f, "p1");
  ASSERT_NE(p1, nullptr);
  EXPECT_EQ(p1->value.ToUint64(), 9u);
  EXPECT_EQ(f.ctx.FindVariable("f1")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("p2")->value.ToUint64(), 9u);
  EXPECT_EQ(f.ctx.FindVariable("f2")->value.ToUint64(), 1u);
}

TEST(SequenceIntersect, AFormalInsideAGroupTakesItsActual) {
  SimFixture f;
  auto* p = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] sv = 10'b0100010000, ev = 10'b0111011000,\n"
      "            gv = 10'b0001000100;\n"
      "  bit s, e, g;\n"
      "  assign s = sv[0]; assign e = ev[0]; assign g = gv[0];\n"
      "  always @(negedge clk) begin\n"
      "    sv <= sv << 1; ev <= ev << 1; gv <= gv << 1;\n"
      "  end\n"
      "  int p = 0, f = 0;\n"
      "  property framed(x);\n"
      "    @(posedge clk) s |-> (x[*3] intersect ##2 g);\n"
      "  endproperty\n"
      "  assert property (framed(e)) p++; else f++;\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->value.ToUint64(), 9u);
  EXPECT_EQ(f.ctx.FindVariable("f")->value.ToUint64(), 1u);
}

}  // namespace
