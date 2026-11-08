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

TEST(SvaEngine, NonConsecutiveRepetition) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kNonConsecutiveRepetition;
  seq.rep_min = 2;
  seq.rep_max = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchNonConsecutiveRepetition(seq, {0, 1, 0, 1, 0}));
  EXPECT_TRUE(MatchNonConsecutiveRepetition(seq, {1, 0, 1}));
  EXPECT_FALSE(MatchNonConsecutiveRepetition(seq, {1, 0, 0}));
}

TEST(SvaEngine, AndRequiresBothOperandsToMatch) {
  EXPECT_TRUE(EvalSequenceAnd(true, true));
  EXPECT_FALSE(EvalSequenceAnd(true, false));
  EXPECT_FALSE(EvalSequenceAnd(false, true));
  EXPECT_FALSE(EvalSequenceAnd(false, false));
}

TEST(SvaEngine, AndEndTimeIsTheLaterOperandEndTime) {
  SequenceAndMatch m = EvalSequenceAndMatch(true, 10, true, 12);
  EXPECT_TRUE(m.matched);
  EXPECT_EQ(m.end_time, 12u);

  SequenceAndMatch swapped = EvalSequenceAndMatch(true, 12, true, 10);
  EXPECT_TRUE(swapped.matched);
  EXPECT_EQ(swapped.end_time, 12u);

  SequenceAndMatch boolean = EvalSequenceAndMatch(true, 1, true, 1);
  EXPECT_TRUE(boolean.matched);
  EXPECT_EQ(boolean.end_time, 1u);

  EXPECT_FALSE(EvalSequenceAndMatch(true, 10, false, 12).matched);
  EXPECT_FALSE(EvalSequenceAndMatch(false, 10, true, 12).matched);
}

TEST(SvaEngine, AndFailsWhenNeitherOperandMatches) {
  EXPECT_FALSE(EvalSequenceAndMatch(false, 10, false, 12).matched);
}

TEST(SequenceAnd, EndsWhereTheLaterOperandEnds) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource(
          "(te1 ##2 te2) and (te3 ##2 te4 ##2 te5)",
          DriveTicks({{1, 2, 8}, {10, 12}, {2, 3, 8}, {4, 10}, {6, 12}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 115u);
}

TEST(SequenceAnd, RangeOperandEndsAtEachLaterTick) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource(
          "(te1 ##[1:5] te2) and (te3 ##2 te4 ##2 te5)",
          DriveTicks(
              {{1, 2, 8}, {9, 10, 11, 12, 13}, {2, 3, 8}, {4, 10}, {6, 12}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 125u);
}

TEST(SequenceAnd, OneOperandMatchingAloneIsNoMatch) {
  const std::string kBody = "(te1 ##2 te2) and (te3 ##2 te4 ##2 te5)";
  SimFixture f;
  auto* first_alone = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{1, 2, 8}, {10, 12}, {}, {}, {}})),
      f, "hits");
  ASSERT_NE(first_alone, nullptr);
  EXPECT_EQ(first_alone->value.ToUint64(), 0u);
  SimFixture g;
  auto* second_alone = RunAndFindVar(
      SequenceTickSource(
          kBody, DriveTicks({{1, 2, 8}, {}, {2, 3, 8}, {4, 10}, {6, 12}})),
      g, "hits");
  ASSERT_NE(second_alone, nullptr);
  EXPECT_EQ(second_alone->value.ToUint64(), 0u);
}

TEST(SequenceAnd, BooleanOperandsMatchWhereBothHold) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource(
          "te1 and te2",
          DriveTicks({{1, 3, 8, 14}, {1, 3, 5, 8, 9, 14}, {}, {}, {}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 135u);
}

}  // namespace
