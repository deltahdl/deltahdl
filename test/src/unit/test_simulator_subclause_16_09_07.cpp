#include <gtest/gtest.h>

#include <algorithm>
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

TEST(SvaEngine, SequenceOperatorOr) {
  EXPECT_TRUE(EvalSequenceOr(true, false));
  EXPECT_TRUE(EvalSequenceOr(false, true));
  EXPECT_TRUE(EvalSequenceOr(true, true));
  EXPECT_FALSE(EvalSequenceOr(false, false));
}

// §16.9.7: the match set of `a or b` is the union of the two operands' match
// sets, with each composite match ending where its originating operand match
// ends. This reproduces Figure 16-11 for `(te1 ##[1:5] te2) or (te3 ##2 te4 ##2
// te5)`: the first operand matches at ticks 9, 10, 11, 12, and 13, and the
// second matches at tick 12. The composite therefore has one match at each of
// ticks 9, 10, 11, and 13 and two matches at tick 12 — operand matches are not
// merged, so the coincident tick appears twice.
TEST(SvaEngine, SequenceOrIsUnionOfOperandMatches) {
  auto u = EvalSequenceOrMatches({9, 10, 11, 12, 13}, {12});
  EXPECT_TRUE(u.matched);
  std::vector<uint32_t> expected{9, 10, 11, 12, 13, 12};
  EXPECT_EQ(u.end_times, expected);
  // The defining feature of the figure: tick 12 carries two composite matches.
  EXPECT_EQ(std::count(u.end_times.begin(), u.end_times.end(), 12u), 2);
}

// §16.9.7: a match of either operand alone is a match of the composite, ending
// at that operand's own end time.
TEST(SvaEngine, SequenceOrMatchesWhenOnlyOneOperandMatches) {
  auto only_a = EvalSequenceOrMatches({7}, {});
  EXPECT_TRUE(only_a.matched);
  EXPECT_EQ(only_a.end_times, std::vector<uint32_t>{7});

  auto only_b = EvalSequenceOrMatches({}, {4});
  EXPECT_TRUE(only_b.matched);
  EXPECT_EQ(only_b.end_times, std::vector<uint32_t>{4});
}

// §16.9.7: with neither operand matching, the composite has no match.
TEST(SvaEngine, SequenceOrHasNoMatchWhenNeitherOperandMatches) {
  auto u = EvalSequenceOrMatches({}, {});
  EXPECT_FALSE(u.matched);
  EXPECT_TRUE(u.end_times.empty());
}

// --- Live cases: the linear sequence monitor over real source ---

// §16.9.7, Figure 16-9: with sampled expressions as operands, te1 or te2
// matches at each tick at least one of them is true. te1 at ticks 1, 3, 6,
// 8, 11, 12 and 14 and te2 at 1, 2, 4, 5, 8, 9, 10 and 14 leave 7 and 13 as
// the ticks neither holds at, so the end point is reached at the twelve
// others, last at the tick at 135.
TEST(SequenceOr, BooleanOperandsMatchWhereEitherHolds) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource("te1 or te2", DriveTicks({{1, 3, 6, 8, 11, 12, 14},
                                                   {1, 2, 4, 5, 8, 9, 10, 14},
                                                   {},
                                                   {},
                                                   {}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 12u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 135u);
}

// §16.9.7, Figure 16-10: each match of either operand is a match of the
// composite, ending where the operand's match ends. te1 at ticks 1, 2 and 8,
// te2 at 10, 12 and 14, te3 at 2, 3 and 8, te4 at 10 and te5 at 12: from tick
// 8, te1 ##2 te2 ends at 10 and te3 ##2 te4 ##2 te5 at 12, so the or ends at
// both, the ticks at 95 and 115.
TEST(SequenceOr, EachOperandMatchIsAMatch) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource(
          "(te1 ##2 te2) or (te3 ##2 te4 ##2 te5)",
          DriveTicks({{1, 2, 8}, {10, 12, 14}, {2, 3, 8}, {10}, {12}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 115u);
}

// §16.9.7, Figure 16-11: with te2 at 9 to 13, te1 ##[1:5] te2 has five
// matches from tick 8, ending at 9 to 13, and te3 ##2 te4 ##2 te5 one at
// 12, so the or's matches are the union, ending at each tick from 9 to 13
// and twice at 12; the end point is reached five times, last at 125.
TEST(SequenceOr, RangeOperandEndsAtEachOfItsTicks) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource(
          "(te1 ##[1:5] te2) or (te3 ##2 te4 ##2 te5)",
          DriveTicks({{1, 2, 8}, {9, 10, 11, 12, 13}, {2, 3, 8}, {10}, {12}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 125u);
}

// §16.9.7: one operand matching is enough. With te3, te4 and te5 never high
// the or ends where te1 ##2 te2 does, at 10; with te2 never high, where
// te3 ##2 te4 ##2 te5 does, at 12.
TEST(SequenceOr, OneOperandMatchingAloneIsAMatch) {
  const std::string kBody = "(te1 ##2 te2) or (te3 ##2 te4 ##2 te5)";
  SimFixture f;
  auto* first_alone = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{1, 2, 8}, {10}, {}, {}, {}})), f,
      "hits");
  ASSERT_NE(first_alone, nullptr);
  EXPECT_EQ(first_alone->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 95u);
  SimFixture g;
  auto* second_alone = RunAndFindVar(
      SequenceTickSource(kBody,
                         DriveTicks({{1, 2, 8}, {}, {2, 3, 8}, {10}, {12}})),
      g, "hits");
  ASSERT_NE(second_alone, nullptr);
  EXPECT_EQ(second_alone->value.ToUint64(), 1u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 115u);
}

}  // namespace
