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

TEST(SvaEngine, WithinContainedSubintervalMatches) {
  auto m = EvalSequenceWithin(SequenceMatchSpan{true, 4, 10},
                              SequenceMatchSpan{true, 3, 11});
  EXPECT_TRUE(m.matched);
  EXPECT_EQ(m.end_time, 11u);
}

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

TEST(SvaEngine, WithinStartNoEarlierThanOuterStart) {
  EXPECT_FALSE(EvalSequenceWithin(SequenceMatchSpan{true, 2, 10},
                                  SequenceMatchSpan{true, 3, 11})
                   .matched);
  EXPECT_TRUE(EvalSequenceWithin(SequenceMatchSpan{true, 3, 10},
                                 SequenceMatchSpan{true, 3, 11})
                  .matched);
}

TEST(SvaEngine, WithinEndNoLaterThanOuterEnd) {
  EXPECT_FALSE(EvalSequenceWithin(SequenceMatchSpan{true, 4, 12},
                                  SequenceMatchSpan{true, 3, 11})
                   .matched);
  EXPECT_TRUE(EvalSequenceWithin(SequenceMatchSpan{true, 4, 11},
                                 SequenceMatchSpan{true, 3, 11})
                  .matched);
}

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

TEST(SequenceWithin, AGroupIsOneOperandOfTheChainAroundIt) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource("te1 ##1 (te4 within te2 ##2 te3)",
                         DriveTicks({{2, 8}, {3, 9}, {5, 11}, {4, 13}, {}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 45u);
}

}  // namespace
