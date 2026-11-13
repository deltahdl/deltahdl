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

TEST(SvaEngine, SequenceThroughout) {
  auto check = [](uint64_t v) { return v == 1; };

  std::vector<uint64_t> values = {1, 1, 1, 1};
  EXPECT_TRUE(EvalThroughout(check, values));

  values = {1, 1, 0, 1};
  EXPECT_FALSE(EvalThroughout(check, values));

  values = {0, 1, 1, 1};
  EXPECT_FALSE(EvalThroughout(check, values));
  values = {1, 1, 1, 0};
  EXPECT_FALSE(EvalThroughout(check, values));

  values = {1};
  EXPECT_TRUE(EvalThroughout(check, values));

  values = {0};
  EXPECT_FALSE(EvalThroughout(check, values));
}

TEST(SvaEngine, SequenceThroughoutEmpty) {
  std::vector<uint64_t> values;
  auto check = [](uint64_t v) { return v == 1; };
  EXPECT_TRUE(EvalThroughout(check, values));
}

TEST(SequenceThroughout, ConditionMustHoldAtEveryTickOfTheMatch) {
  const std::string kBody = "te1 throughout (te2 ##2 te3)";
  SimFixture f;
  auto* held = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{3, 4, 5}, {3}, {5}, {}, {}})), f,
      "hits");
  ASSERT_NE(held, nullptr);
  EXPECT_EQ(held->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 45u);
  SimFixture g;
  auto* broken = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{3, 5}, {3}, {5}, {}, {}})), g,
      "hits");
  ASSERT_NE(broken, nullptr);
  EXPECT_EQ(broken->value.ToUint64(), 0u);
}

TEST(SequenceThroughout, IntervalBeginsWhereTheGuardedSequenceBegins) {
  const std::string kBody = "te1 throughout (##2 te2)";
  SimFixture f;
  auto* held = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{3, 4, 5}, {5}, {}, {}, {}})), f,
      "hits");
  ASSERT_NE(held, nullptr);
  EXPECT_EQ(held->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 45u);
  SimFixture g;
  auto* broken = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{4, 5}, {5}, {}, {}, {}})), g,
      "hits");
  ASSERT_NE(broken, nullptr);
  EXPECT_EQ(broken->value.ToUint64(), 0u);
}

TEST(SequenceThroughout, ConditionIsReadAtTheLastTick) {
  const std::string kBody = "te1 throughout (te2 ##1 te3)";
  SimFixture f;
  auto* held = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{3, 4}, {3}, {4}, {}, {}})), f,
      "hits");
  ASSERT_NE(held, nullptr);
  EXPECT_EQ(held->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
  SimFixture g;
  auto* broken = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{3}, {3}, {4}, {}, {}})), g,
      "hits");
  ASSERT_NE(broken, nullptr);
  EXPECT_EQ(broken->value.ToUint64(), 0u);
}

TEST(SequenceThroughout, BurstRule1MatchesOnlyWithBurstModeLowThroughout) {
  const std::string kBody =
      "$fell(te1) ##0 ((!te1) throughout (##2 ((te3==0)&&(te2==0)) [*7]))";
  const std::vector<int> kIrdy = {1, 2, 12, 13, 14};
  const std::vector<int> kTrdy = {1, 2, 3, 11, 12, 13, 14};
  SimFixture f;
  auto* fails = RunAndFindVar(
      SequenceTickSource(
          kBody,
          DriveTicks({{1, 9, 10, 11, 12, 13, 14}, kIrdy, kTrdy, {}, {}})),
      f, "hits");
  ASSERT_NE(fails, nullptr);
  EXPECT_EQ(fails->value.ToUint64(), 0u);
  SimFixture g;
  auto* succeeds = RunAndFindVar(
      SequenceTickSource(kBody,
                         DriveTicks({{1, 12, 13, 14}, kIrdy, kTrdy, {}, {}})),
      g, "hits");
  ASSERT_NE(succeeds, nullptr);
  EXPECT_EQ(succeeds->value.ToUint64(), 1u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 95u);
}

struct EndPoints {
  uint64_t hits;
  uint64_t last;
};

EndPoints EndPointsOf(const std::string& body, const std::string& drive) {
  SimFixture f;
  auto* hits = RunAndFindVar(SequenceTickSource(body, drive), f, "hits");
  if (hits == nullptr) return {~0ull, ~0ull};
  return {hits->value.ToUint64(), f.ctx.FindVariable("last")->value.ToUint64()};
}

void ExpectOneEndUnlessBroken(const std::string& body, const std::string& held,
                              uint64_t last, const std::string& broken) {
  EndPoints ends = EndPointsOf(body, held);
  EXPECT_EQ(ends.hits, 1u) << body;
  EXPECT_EQ(ends.last, last) << body;
  EXPECT_EQ(EndPointsOf(body, broken).hits, 0u) << body;
}

TEST(SequenceThroughout, AnIntervalAfterARangedDelayBeginsAtItsFirstOperand) {
  const std::string kHeld = DriveTicks({{5}, {3}, {5}, {}, {}});
  const std::string kBroken = DriveTicks({{4}, {3}, {5}, {}, {}});
  ExpectOneEndUnlessBroken("te2 ##[1:2] (te1 throughout te3)", kHeld, 45,
                           kBroken);
  ExpectOneEndUnlessBroken("te2 ##2 (te1 throughout te3)", kHeld, 45, kBroken);
}

TEST(SequenceThroughout, AnIntervalAfterAnUnboundedDelayBeginsAtItsOperand) {
  ExpectOneEndUnlessBroken("te2 ##[1:$] (te1 throughout te3 ##1 te4)",
                           DriveTicks({{5, 6}, {2}, {5}, {6}, {}}), 55,
                           DriveTicks({{5}, {2}, {5}, {6}, {}}));
}

TEST(SequenceThroughout, ASequenceOpeningWithADelayAfterARangeIsGuarded) {
  const std::string kHeld = DriveTicks({{5, 6, 7}, {3}, {7}, {}, {}});
  const std::string kBroken = DriveTicks({{6, 7}, {3}, {7}, {}, {}});
  ExpectOneEndUnlessBroken("te2 ##[1:2] (te1 throughout ##2 te3)", kHeld, 65,
                           kBroken);
  ExpectOneEndUnlessBroken("te2 ##2 (te1 throughout ##2 te3)", kHeld, 65,
                           kBroken);
}

TEST(SequenceThroughout, AGuardedSequenceOpeningWithARangedDelayIsGuarded) {
  ExpectOneEndUnlessBroken("te1 throughout ##[1:2] te3",
                           DriveTicks({{3, 4, 5}, {}, {5}, {}, {}}), 45,
                           DriveTicks({{3, 5}, {}, {5}, {}, {}}));
}

}  // namespace
