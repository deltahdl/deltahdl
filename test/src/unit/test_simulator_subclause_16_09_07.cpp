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

TEST(SvaEngine, SequenceOperatorOr) {
  EXPECT_TRUE(EvalSequenceOr(true, false));
  EXPECT_TRUE(EvalSequenceOr(false, true));
  EXPECT_TRUE(EvalSequenceOr(true, true));
  EXPECT_FALSE(EvalSequenceOr(false, false));
}

TEST(SvaEngine, SequenceOrIsUnionOfOperandMatches) {
  auto u = EvalSequenceOrMatches({9, 10, 11, 12, 13}, {12});
  EXPECT_TRUE(u.matched);
  std::vector<uint32_t> expected{9, 10, 11, 12, 13, 12};
  EXPECT_EQ(u.end_times, expected);
  EXPECT_EQ(std::count(u.end_times.begin(), u.end_times.end(), 12u), 2);
}

TEST(SvaEngine, SequenceOrMatchesWhenOnlyOneOperandMatches) {
  auto only_a = EvalSequenceOrMatches({7}, {});
  EXPECT_TRUE(only_a.matched);
  EXPECT_EQ(only_a.end_times, std::vector<uint32_t>{7});

  auto only_b = EvalSequenceOrMatches({}, {4});
  EXPECT_TRUE(only_b.matched);
  EXPECT_EQ(only_b.end_times, std::vector<uint32_t>{4});
}

TEST(SvaEngine, SequenceOrHasNoMatchWhenNeitherOperandMatches) {
  auto u = EvalSequenceOrMatches({}, {});
  EXPECT_FALSE(u.matched);
  EXPECT_TRUE(u.end_times.empty());
}

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

TEST(SequenceOr, AGroupIsOneOperandOfTheChainAroundIt) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource("te1 ##1 (te2 ##1 te3 or te4) ##1 te5",
                         DriveTicks({{2}, {3}, {4}, {3}, {4, 5}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 45u);
}

TEST(SequenceOr, AnInstanceIsOneOperandOfTheChainAroundIt) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceTickSource("te1 ##1 alt ##1 te5",
                                       DriveTicks({{2}, {3}, {4}, {3}, {4, 5}}),
                                       "  sequence alt;\n"
                                       "    te2 ##1 te3 or te4;\n"
                                       "  endsequence\n"),
                    f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 45u);
}

TEST(SequenceOr, AFormalInsideAGroupTakesItsActual) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceTickSource(
                        "framed(te4)", DriveTicks({{2}, {3}, {4}, {3}, {4, 5}}),
                        "  sequence framed(x);\n"
                        "    te1 ##1 (te2 ##1 te3 or x) ##1 te5;\n"
                        "  endsequence\n"),
                    f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 45u);
}

}  // namespace
