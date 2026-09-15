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

// §16.9.9: `exp throughout seq` matches only when the condition holds at every
// clock tick spanned by the sequence match. A single tick where the condition
// is false defeats the whole match, no matter where in the interval it falls.
TEST(SvaEngine, SequenceThroughout) {
  auto check = [](uint64_t v) { return v == 1; };

  // Condition true at every tick: the composite matches.
  std::vector<uint64_t> values = {1, 1, 1, 1};
  EXPECT_TRUE(EvalThroughout(check, values));

  // A false tick in the interior breaks the match.
  values = {1, 1, 0, 1};
  EXPECT_FALSE(EvalThroughout(check, values));

  // The interval boundaries count just as much as the interior: a violation at
  // the first or the last tick is equally fatal. These cases pin the iteration
  // to span the whole interval rather than skipping an end.
  values = {0, 1, 1, 1};
  EXPECT_FALSE(EvalThroughout(check, values));
  values = {1, 1, 1, 0};
  EXPECT_FALSE(EvalThroughout(check, values));

  // A minimal single-tick interval with the condition held still matches.
  values = {1};
  EXPECT_TRUE(EvalThroughout(check, values));

  // The complementary boundary: a single-tick interval whose only tick violates
  // the condition does not match. This is the dividing line against the empty
  // interval — one present tick must satisfy exp, whereas an absent tick cannot
  // fail it (see SequenceThroughoutEmpty).
  values = {0};
  EXPECT_FALSE(EvalThroughout(check, values));
}

// §16.9.9: the construct abbreviates `(exp)[*0:$] intersect seq`, whose
// `[*0:$]` admits a zero-length match. Over an empty interval there is no tick
// at which the condition could fail, so the throughout condition is vacuously
// held.
TEST(SvaEngine, SequenceThroughoutEmpty) {
  std::vector<uint64_t> values;
  auto check = [](uint64_t v) { return v == 1; };
  EXPECT_TRUE(EvalThroughout(check, values));
}

// --- Live cases: the linear sequence monitor over real source ---

// §16.9.9: `te1 throughout (te2 ##2 te3)` matches where te2 ##2 te3 does and
// te1 holds at every tick of the match. With te2 at tick 3 and te3 at 5 the
// sequence matches from 3 to 5, so with te1 high at 3, 4 and 5 the whole ends
// at 5, the tick at 45, and with te1 low at 4 alone it does not.
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

// §16.9.9: the interval te1 must hold over begins where the guarded
// sequence begins, not where its first operand is read: `te1 throughout (##2
// te2)` from tick 3, with te2 at 5, needs te1 at 3, 4 and 5, so with te1 low
// at 3 the attempt from 3 has no match and, te2 being high at 5 alone, no
// other attempt has one either.
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

// §16.9.9: the condition is read at the last tick of the match as at the
// first. `te1 throughout (te2 ##1 te3)` with te2 at 3 and te3 at 4 ends at 4,
// the tick at 35, with te1 high at 3 and 4, and not with te1 high at 3 alone.
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

// §16.9.9, Figures 16-12 and 16-13: the clause's burst_rule1 with te1 as
// burst_mode, te2 as irdy and te3 as trdy. burst_mode is high at tick 1 and
// falls at 2, irdy is high at 1 and 2 and trdy at 1 to 3, so (trdy==0) &&
// (irdy==0) holds at 4 to 10, seven ticks from two after the fall; with
// burst_mode high again from 9 the attempt from 2 fails at 9, and with it low
// through 11 the sequence ends at 10, the tick at 95.
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

}  // namespace
