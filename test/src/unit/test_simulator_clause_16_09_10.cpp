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

}  // namespace
