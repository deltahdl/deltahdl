#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"

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

}  // namespace
