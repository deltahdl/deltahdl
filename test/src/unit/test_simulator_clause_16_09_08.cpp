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

TEST(SvaEngine, SequenceOperatorIntersect) {
  EXPECT_TRUE(EvalSequenceIntersect(true, true, 3, 3));

  EXPECT_FALSE(EvalSequenceIntersect(true, true, 3, 4));
  EXPECT_FALSE(EvalSequenceIntersect(true, false, 3, 3));
}

// §16.9.8: when the operand sequence has no match, first_match has no match.
TEST(SvaEngine, FirstMatchHasNoMatchWhenOperandDoesNotMatch) {
  auto fm = EvalFirstMatch({});
  EXPECT_FALSE(fm.matched);
  EXPECT_TRUE(fm.end_times.empty());
}

// §16.9.8: the operand match with the earliest ending clock tick is the match
// of first_match; every later-ending match is discarded. The variable-delay
// example te1 ##[2:5] te2 can end on ticks 2, 3, 4, or 5 after the start, so
// first_match keeps only the soonest completion.
TEST(SvaEngine, FirstMatchKeepsOnlyEarliestEndingMatch) {
  auto fm = EvalFirstMatch({5, 3, 4, 2});
  EXPECT_TRUE(fm.matched);
  EXPECT_EQ(fm.end_times, std::vector<uint32_t>{2});
}

// §16.9.8: when several operand matches share the earliest ending clock tick,
// all of them are matches of first_match. The (a ##2 b) or (c ##2 d) example
// can have a ##2 b and c ##2 d ending on the same tick, so both survive.
TEST(SvaEngine, FirstMatchKeepsAllMatchesSharingEarliestEndTick) {
  auto fm = EvalFirstMatch({4, 4, 6});
  EXPECT_TRUE(fm.matched);
  std::vector<uint32_t> expected{4, 4};
  EXPECT_EQ(fm.end_times, expected);
}

// §16.9.8 edge case: an operand with a single match has nothing later to
// discard, so first_match yields that one match unchanged.
TEST(SvaEngine, FirstMatchKeepsSingleOperandMatch) {
  auto fm = EvalFirstMatch({7});
  EXPECT_TRUE(fm.matched);
  EXPECT_EQ(fm.end_times, std::vector<uint32_t>{7});
}

// §16.9.8 edge case: when every operand match ends on the same tick, that tick
// is the earliest, so none is discarded and all are retained.
TEST(SvaEngine, FirstMatchRetainsAllWhenEveryMatchTiesOnSameTick) {
  auto fm = EvalFirstMatch({3, 3, 3});
  EXPECT_TRUE(fm.matched);
  std::vector<uint32_t> expected{3, 3, 3};
  EXPECT_EQ(fm.end_times, expected);
}

}
