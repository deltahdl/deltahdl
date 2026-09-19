#include <gtest/gtest.h>

#include <cstdint>
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

// --- Live cases: the linear sequence monitor over real source ---

// §16.9.8: an attempt of first_match(seq) matches only where the earliest
// ending match of seq's attempt ends. With te1 at tick 1 and te2 at 3 to 6,
// the clause's t1, te1 ##[2:5] te2, ends at 3, 4, 5 and 6 from tick 1, and
// its ts1, first_match(te1 ##[2:5] te2), at 3 alone, the tick at 25.
TEST(SequenceFirstMatch, KeepsTheEarliestEndingMatchOfAnAttempt) {
  const std::string kDrive = DriveTicks({{1}, {3, 4, 5, 6}, {}, {}, {}});
  SimFixture f;
  auto* all =
      RunAndFindVar(SequenceTickSource("te1 ##[2:5] te2", kDrive), f, "hits");
  ASSERT_NE(all, nullptr);
  EXPECT_EQ(all->value.ToUint64(), 4u);
  SimFixture g;
  auto* first = RunAndFindVar(
      SequenceTickSource("first_match(te1 ##[2:5] te2)", kDrive), g, "hits");
  ASSERT_NE(first, nullptr);
  EXPECT_EQ(first->value.ToUint64(), 1u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 25u);
}

// §16.9.8: where the operand's attempt has no match, first_match has none.
TEST(SequenceFirstMatch, HasNoMatchWhereTheOperandHasNone) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceTickSource("first_match(te1 ##[2:5] te2)",
                                       DriveTicks({{1}, {2, 7}, {}, {}, {}})),
                    f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 0u);
}

// §16.9.8: the earliest end is taken over every `or` operand of the
// operand's attempt. With te1 and te3 at tick 1, te2 at 3 and 4 and te4 at 2,
// (te1 ##[2:3] te2) or (te3 ##[1:2] te4), the clause's t2 over other names,
// ends at 2, 3 and 4 from tick 1, and first_match of it at 2 alone, the tick
// at 15; with te4 at 3 instead, the two matches ending at 3 are both matches
// of the first_match, which ends at 3, the tick at 25, and not at 4.
TEST(SequenceFirstMatch, TakesTheEarliestEndOverTheOrOperands) {
  const std::string kBody =
      "first_match((te1 ##[2:3] te2) or (te3 ##[1:2] te4))";
  SimFixture f;
  auto* second_first = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{1}, {3, 4}, {1}, {2}, {}})), f,
      "hits");
  ASSERT_NE(second_first, nullptr);
  EXPECT_EQ(second_first->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 15u);
  SimFixture g;
  auto* tied = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{1}, {3, 4}, {1}, {3}, {}})), g,
      "hits");
  ASSERT_NE(tied, nullptr);
  EXPECT_EQ(tied->value.ToUint64(), 1u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 25u);
}

// §16.9.8: the attempts are told apart. With te1 at ticks 1 and 2 and te2 at
// 3 to 6, the attempt from 1 ends first at 3 and the one from 2 at 4, so
// first_match(te1 ##[2:5] te2) ends at 3 and at 4, the ticks at 25 and 35,
// the attempts' later matches at 5 and 6 discarded.
TEST(SequenceFirstMatch, EachAttemptKeepsItsOwnEarliestMatch) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource("first_match(te1 ##[2:5] te2)",
                         DriveTicks({{1, 2}, {3, 4, 5, 6}, {}, {}, {}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
}

}  // namespace
