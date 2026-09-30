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

// §16.9.6: `intersect` matches only when both operand sequences match. Unlike
// `and`, the operands must additionally share the same end time, i.e. the two
// operand matches must have the same length.
TEST(SvaEngine, IntersectRequiresBothOperandsToMatch) {
  // Equal lengths, both matching: the composite matches.
  EXPECT_TRUE(EvalSequenceIntersect(true, true, 5, 5));

  // A non-matching operand defeats the composite even at equal length.
  EXPECT_FALSE(EvalSequenceIntersect(true, false, 5, 5));
  EXPECT_FALSE(EvalSequenceIntersect(false, true, 5, 5));
  EXPECT_FALSE(EvalSequenceIntersect(false, false, 5, 5));
}

// §16.9.6: the length restriction is the basic difference between `and` and
// `intersect`. When both operands match but their match lengths differ, `and`
// would still match (its end time is the later of the two), whereas `intersect`
// finds no same-length pair and therefore does not match.
TEST(SvaEngine, IntersectRequiresEqualMatchLengths) {
  // Mirrors Figure 16-8 vs Figure 16-6: with operands ending at ticks 12 and
  // 10, `and` matches but `intersect` does not.
  EXPECT_TRUE(EvalSequenceAnd(true, true));
  EXPECT_FALSE(EvalSequenceIntersect(true, true, 4, 6));
  EXPECT_FALSE(EvalSequenceIntersect(true, true, 6, 4));

  // A Boolean-style single-tick pair shares length 1, so intersect matches.
  EXPECT_TRUE(EvalSequenceIntersect(true, true, 1, 1));
}

// §16.9.6: an intersect attempt can yield multiple matches, computed by pairing
// same-length matches of the two operands. Each pair produces one composite
// match carrying the shared length and match point of the pair.
TEST(SvaEngine, IntersectPairsEqualLengthOperandMatches) {
  // Mirrors Figure 16-8: the first operand `te1 ##[1:5] te2` matches with
  // lengths 1..5 (match points 9..13 from a start at tick 8); the second
  // operand `te3 ##2 te4 ##2 te5` matches once with length 5 (match point 13).
  std::vector<IntersectOperandMatch> a = {
      {1, 9}, {2, 10}, {3, 11}, {4, 12}, {5, 13}};
  std::vector<IntersectOperandMatch> b = {{5, 13}};

  auto matches = EvalSequenceIntersectMatches(a, b);

  // Only the length-5 matches pair, yielding a single composite match whose
  // length and match point are the shared ones.
  ASSERT_EQ(matches.size(), 1u);
  EXPECT_EQ(matches[0].length, 5u);
  EXPECT_EQ(matches[0].match_point, 13u);
}

// §16.9.6: when several matches share a length across the two operands, every
// resulting pair is a separate composite match.
TEST(SvaEngine, IntersectYieldsOneCompositeMatchPerEqualLengthPair) {
  std::vector<IntersectOperandMatch> a = {{2, 5}, {3, 6}};
  std::vector<IntersectOperandMatch> b = {{2, 5}, {3, 6}, {4, 7}};

  auto matches = EvalSequenceIntersectMatches(a, b);

  // The length-2 and length-3 pairs both match; the length-4 second-operand
  // match has no first-operand partner and is dropped.
  ASSERT_EQ(matches.size(), 2u);
  EXPECT_EQ(matches[0].length, 2u);
  EXPECT_EQ(matches[0].match_point, 5u);
  EXPECT_EQ(matches[1].length, 3u);
  EXPECT_EQ(matches[1].match_point, 6u);
}

// §16.9.6: if no equal-length pair exists, there is no match of the composite
// sequence — even though both operands match on their own.
TEST(SvaEngine, IntersectHasNoMatchWithoutAnEqualLengthPair) {
  std::vector<IntersectOperandMatch> a = {{2, 5}, {3, 6}};
  std::vector<IntersectOperandMatch> b = {{4, 7}, {5, 8}};

  EXPECT_TRUE(EvalSequenceIntersectMatches(a, b).empty());

  // An empty operand match set (that operand never matched) likewise yields no
  // composite match.
  EXPECT_TRUE(EvalSequenceIntersectMatches(a, {}).empty());
  EXPECT_TRUE(EvalSequenceIntersectMatches({}, b).empty());
}

// --- Live cases: the linear sequence monitor over real source ---

// §16.9.6, Figure 16-8: te1 at ticks 1, 2 and 8; te2 at 9 to 13; te3 at 2, 3
// and 8; te4 at 4 and 10; te5 at 6 and 12. From tick 8, te1 ##[1:5] te2 has
// five matches ending at 9 to 13 and te3 ##2 te4 ##2 te5 one ending at 12,
// and only the pair of the same length matches the intersection, ending at
// 12, the tick at 115, where the and of §16.9.5 would end at 13 as well.
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

// §16.9.6: both operands matching is not enough; with te2 at 10 alone,
// te1 ##[1:5] te2 ends at 10 and te3 ##2 te4 ##2 te5 at 12 from the same
// tick 8, lengths that differ, so the intersection has no match.
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

// §16.9.6: an attempt can have several matches, one per pair of the same
// length. With te2 at 10 and 12 and te5 at 10 and 12 as well, the pairs of
// length two and four both match, so the end point is reached at the ticks
// at 95 and 115; and a match of the first operand from tick 1 or 2, where te2
// is low, has nothing to pair with.
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

// §16.9.1: `intersect` binds tighter than `and`, so `te1 ##2 te2 intersect
// te3 ##2 te4 and te3 ##2 te4 ##2 te5` is the intersection of the two
// two-tick operands, which ends at 10 from tick 8, and-ed with the four-tick
// one, which ends at 12, so the whole ends at 12, the tick at 115; read with
// `and` binding tighter, the and would end at 12 alone, four ticks long, and
// the two-tick te1 ##2 te2 would have nothing to pair with.
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

// §16.9.6 and §16.7: an intersection written as a group is one operand of
// the chain around it, begun where the delay before it is up and the chain
// going on from its match. From tick 2 the group begins at 3, where
// te2[*1:2] ends at 3 or 4 and te3 ##1 te4 at 4, so the pair of length two
// ends at 4 and te5 is read at 5, the tick at 45; from tick 7 te2[*1:2] ends
// at 8 alone and te3 ##1 te4 at 9, lengths that differ, so the te5 at 10
// that an `and` would reach is never read.
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

// §16.8: an instance of a named sequence whose body is an intersection
// behaves as that body does, so as one operand of a chain it matches as the
// group of the case above does.
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

// §16.9.6 and §16.12.7: a grouped intersection is a consequent and part of
// an antecedent. s is high at ticks 1 and 5, e at 1 to 3, 5 and 6, and g at
// 3 and 7. From 1, e[*3] and ##2 g both end at 3; from 5, e is low at 7. So
// the consequent holds from 1 and fails from 5, and the antecedent matches
// from 1 alone, ending at 3, with e low at 4; every other attempt of either
// is vacuous.
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

// §16.12.1 and §16.9.6: the actual of a property's formal stands for the
// formal inside a grouped intersection too. With `e` bound to x, the
// property is the implication of the case above, holding from 1 and failing
// from 5, where a formal left unbound inside the group would fail from 1 as
// well.
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
