#include <gtest/gtest.h>

#include <string>
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

// §16.9.10: `seq1 within seq2` matches along an interval when seq2 matches the
// whole interval and seq1 matches some contained subinterval. When seq1's match
// sits strictly inside seq2's, the containment matches and completes at seq2's
// match point. Mirrors the !trdy[*7] within ($fell(irdy) ##1 irdy[*8]) example,
// which matches from clock tick 3 to clock tick 11.
TEST(SvaEngine, WithinContainedSubintervalMatches) {
  // seq2 spans ticks [3,11]; seq1 spans the contained [4,10].
  auto m = EvalSequenceWithin(
      SequenceMatchSpan{/*matched=*/true, /*start_time=*/4, /*end_time=*/10},
      SequenceMatchSpan{/*matched=*/true, /*start_time=*/3, /*end_time=*/11});
  EXPECT_TRUE(m.matched);
  // The composite spans seq2's interval, so it completes when seq2 completes.
  EXPECT_EQ(m.end_time, 11u);
}

// §16.9.10: both operands shall match. A non-matching operand defeats the
// containment even when the time bounds would otherwise be satisfied.
TEST(SvaEngine, WithinRequiresBothOperandsToMatch) {
  EXPECT_FALSE(EvalSequenceWithin(SequenceMatchSpan{false, 4, 10},
                                  SequenceMatchSpan{true, 3, 11})
                   .matched);
  EXPECT_FALSE(EvalSequenceWithin(SequenceMatchSpan{true, 4, 10},
                                  SequenceMatchSpan{false, 3, 11})
                   .matched);
  EXPECT_FALSE(EvalSequenceWithin(SequenceMatchSpan{false, 4, 10},
                                  SequenceMatchSpan{false, 3, 11})
                   .matched);
}

// §16.9.10 first bullet: the start point of seq1 shall be no earlier than the
// start point of seq2. A seq1 match that begins before seq2 does is not
// contained and so does not match. Coincident starts are allowed (no earlier).
TEST(SvaEngine, WithinStartNoEarlierThanOuterStart) {
  // seq1 starts at tick 2, before seq2's start at 3: not contained.
  EXPECT_FALSE(EvalSequenceWithin(SequenceMatchSpan{true, 2, 10},
                                  SequenceMatchSpan{true, 3, 11})
                   .matched);
  // Coincident start at tick 3 satisfies the "no earlier" bound.
  EXPECT_TRUE(EvalSequenceWithin(SequenceMatchSpan{true, 3, 10},
                                 SequenceMatchSpan{true, 3, 11})
                  .matched);
}

// §16.9.10 second bullet: the match point of seq1 shall be no later than the
// match point of seq2. A seq1 match completing after seq2 is not contained.
// Coincident completion points are allowed (no later).
TEST(SvaEngine, WithinEndNoLaterThanOuterEnd) {
  // seq1 completes at tick 12, after seq2's completion at 11: not contained.
  EXPECT_FALSE(EvalSequenceWithin(SequenceMatchSpan{true, 4, 12},
                                  SequenceMatchSpan{true, 3, 11})
                   .matched);
  // Coincident completion at tick 11 satisfies the "no later" bound.
  EXPECT_TRUE(EvalSequenceWithin(SequenceMatchSpan{true, 4, 11},
                                 SequenceMatchSpan{true, 3, 11})
                  .matched);
}

// --- Live cases: the linear sequence monitor over real source ---

// §16.9.10: `te1[*2] within (te2 ##1 te3[*3])` matches where the outer
// sequence does and te1[*2] matches along a subinterval of it. With te2 at
// tick 3 and te3 at 4 to 6 the outer matches from 3 to 6, so with te1 at 4
// and 5 the whole ends at 6, the tick at 55.
TEST(SequenceWithin, MatchesWhereTheInnerLiesInsideTheOuter) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource("te1[*2] within (te2 ##1 te3[*3])",
                         DriveTicks({{4, 5}, {3}, {4, 5, 6}, {}, {}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
}

// §16.9.10: the inner match may start where the outer does and end where
// it does. With te1 at 3 to 6, te1[*4] matches from 3 to 6 as the outer
// does, and the whole ends at 6, the tick at 55.
TEST(SequenceWithin, InnerMayCoincideWithTheOuter) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource("te1[*4] within (te2 ##1 te3[*3])",
                         DriveTicks({{3, 4, 5, 6}, {3}, {4, 5, 6}, {}, {}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
}

// §16.9.10: the inner match may start no earlier than the outer and end no
// later. te1 at 2 and 3 gives te1[*2] a match from 2, before the outer's 3,
// and te1 at 6 and 7 one ending at 7, after the outer's 6; neither is a match
// of the whole.
TEST(SequenceWithin, InnerMayNotReachOutsideTheOuter) {
  const std::string kBody = "te1[*2] within (te2 ##1 te3[*3])";
  SimFixture f;
  auto* early = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{2, 3}, {3}, {4, 5, 6}, {}, {}})),
      f, "hits");
  ASSERT_NE(early, nullptr);
  EXPECT_EQ(early->value.ToUint64(), 0u);
  SimFixture g;
  auto* late = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{6, 7}, {3}, {4, 5, 6}, {}, {}})),
      g, "hits");
  ASSERT_NE(late, nullptr);
  EXPECT_EQ(late->value.ToUint64(), 0u);
}

// §16.9.10: the clause's `!trdy[*7] within ($fell(irdy) ##1 !irdy[*8])`
// over Figure 16-13's trace, te2 as irdy, high at 1 and 2 and from 12, and
// te3 as trdy, high at 1 to 3 and from 11: the outer matches from 3, where
// irdy falls, to 11, and !trdy[*7] from 4 to 10 inside it, so the whole ends
// at 11, the tick at 105.
TEST(SequenceWithin, ClauseExampleMatchesFromTickThreeToEleven) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource(
          "!te3[*7] within ($fell(te2) ##1 !te2[*8])",
          DriveTicks(
              {{}, {1, 2, 12, 13, 14}, {1, 2, 3, 11, 12, 13, 14}, {}, {}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 105u);
}

}  // namespace
