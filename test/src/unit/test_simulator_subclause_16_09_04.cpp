#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "builders_systask.h"
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
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

TEST(SvaEngine, GotoRepetition) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kGotoRepetition;
  seq.rep_min = 2;
  seq.rep_max = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchGotoRepetition(seq, {0, 1, 0, 1}));

  EXPECT_FALSE(MatchGotoRepetition(seq, {0, 1, 0, 0}));
}

TEST(SvaEngine, GotoRepetitionEndsAtMatch) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kGotoRepetition;
  seq.rep_min = 1;
  seq.rep_max = 1;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchGotoRepetition(seq, {0, 0, 1}));
  EXPECT_FALSE(MatchGotoRepetition(seq, {0, 1, 0}));
}

// §16.9.4: $rose_gclk/$fell_gclk report the LSB changing to 1 / to 0 between
// the preceding and current global clock ticks.
TEST(GlobalClockingSampledValue, PastEdgeFunctions) {
  EXPECT_TRUE(RoseGclk(/*prev_lsb=*/0, /*cur_lsb=*/1));
  EXPECT_FALSE(RoseGclk(/*prev_lsb=*/1, /*cur_lsb=*/1));
  EXPECT_TRUE(FellGclk(/*prev_lsb=*/1, /*cur_lsb=*/0));
  EXPECT_FALSE(FellGclk(/*prev_lsb=*/0, /*cur_lsb=*/0));
}

// §16.9.4: $stable_gclk reports the whole expression unchanged and
// $changed_gclk reports it changed across global clock ticks.
TEST(GlobalClockingSampledValue, PastStableAndChanged) {
  EXPECT_TRUE(StableGclk(/*prev_value=*/5, /*cur_value=*/5));
  EXPECT_FALSE(StableGclk(/*prev_value=*/5, /*cur_value=*/6));
  EXPECT_TRUE(ChangedGclk(/*prev_value=*/5, /*cur_value=*/6));
  EXPECT_FALSE(ChangedGclk(/*prev_value=*/5, /*cur_value=*/5));
}

// §16.9.4: the future functions use the subsequent value; $rising_gclk and
// $falling_gclk report the LSB changing to 1 / to 0 at the next global tick.
TEST(GlobalClockingSampledValue, FutureEdgeFunctions) {
  EXPECT_TRUE(RisingGclk(/*cur_lsb=*/0, /*next_lsb=*/1));
  EXPECT_FALSE(RisingGclk(/*cur_lsb=*/1, /*next_lsb=*/1));
  EXPECT_TRUE(FallingGclk(/*cur_lsb=*/1, /*next_lsb=*/0));
  EXPECT_FALSE(FallingGclk(/*cur_lsb=*/0, /*next_lsb=*/0));
}

// §16.9.4: $changing_gclk is the complement of $steady_gclk.
TEST(GlobalClockingSampledValue, ChangingIsComplementOfSteady) {
  EXPECT_TRUE(SteadyGclk(/*cur_value=*/3, /*next_value=*/3));
  EXPECT_FALSE(SteadyGclk(/*cur_value=*/3, /*next_value=*/4));
  EXPECT_EQ(ChangingGclk(3, 3), !SteadyGclk(3, 3));
  EXPECT_EQ(ChangingGclk(3, 4), !SteadyGclk(3, 4));
}

// §16.9.4: the action block of an assertion using global clocking future
// sampled value functions, including a default $error (see §16.14.1), is
// delayed to the global clock tick that follows the last assertion-clock tick.
TEST(GlobalClockingSampledValue, FutureActionBlockDelayedToFollowingTick) {
  EXPECT_TRUE(GclkFutureActionBlockDelayedToFollowingGlobalTick());
}

// §16.9.4: a $assertcontrol Kill (control_type 5, see §20.11) affects the
// attempt only when it occurs at or before the last assertion-clock tick, not
// in a later time step up to the following global clock tick.
TEST(GlobalClockingSampledValue, FutureKillTimingBoundsTheAttempt) {
  EXPECT_TRUE(GclkFutureKillAffectsAttempt(
      /*kill_at_or_before_last_assertion_tick=*/true));
  EXPECT_FALSE(GclkFutureKillAffectsAttempt(
      /*kill_at_or_before_last_assertion_tick=*/false));
}

// §16.9.4 (Example 3): disable iff is the first-named asynchronous control that
// acts with respect to the evaluation-attempt interval. With the attempt
// interval ending at time 80 and the disable condition rst becoming active only
// at time 82, the attempt is not disabled even though rst is active before the
// delayed action block executes at time 90; a disable condition active no later
// than time 80 would disable the attempt.
TEST(GlobalClockingSampledValue, FutureDisableIffBoundedByAttemptInterval) {
  EXPECT_FALSE(GclkFutureAttemptDisabledByDisableIff(
      /*disable_active_time=*/82, /*attempt_interval_end_time=*/80));
  EXPECT_TRUE(GclkFutureAttemptDisabledByDisableIff(
      /*disable_active_time=*/80, /*attempt_interval_end_time=*/80));
}

// §16.9.4: $past_gclk and $future_gclk are value-bearing functions; the
// evaluator recognizes them and yields the (sampled) value of their argument.
TEST(GlobalClockingSampledValue, EvalValueBearingFunctions) {
  SysTaskFixture f;
  auto* past = MkSysCall(f.arena, "$past_gclk", {MkInt(f.arena, 42)});
  EXPECT_EQ(EvalExpr(past, f.ctx, f.arena).ToUint64(), 42u);
  auto* future = MkSysCall(f.arena, "$future_gclk", {MkInt(f.arena, 7)});
  EXPECT_EQ(EvalExpr(future, f.ctx, f.arena).ToUint64(), 7u);
}

// §16.9.4: the global clocking value-change functions are recognized by the
// evaluator and return a 1-bit Boolean result.
TEST(GlobalClockingSampledValue, EvalValueChangeFunctionsAreOneBit) {
  SysTaskFixture f;
  auto* rose = MkSysCall(f.arena, "$rose_gclk", {MkInt(f.arena, 1)});
  EXPECT_EQ(EvalExpr(rose, f.ctx, f.arena).width, 1u);
  auto* changing = MkSysCall(f.arena, "$changing_gclk", {MkInt(f.arena, 1)});
  EXPECT_EQ(EvalExpr(changing, f.ctx, f.arena).width, 1u);
}

// §16.9.4: $rose_gclk/$fell_gclk and the future $rising_gclk/$falling_gclk are
// defined on the LSB of the expression, so only bit 0 of a wider value matters.
TEST(GlobalClockingSampledValue, EdgeFunctionsUseLeastSignificantBit) {
  EXPECT_TRUE(RoseGclk(/*prev_lsb=*/0b10, /*cur_lsb=*/0b11));   // LSB 0 -> 1
  EXPECT_FALSE(RoseGclk(/*prev_lsb=*/0b11, /*cur_lsb=*/0b10));  // LSB 1 -> 0
  EXPECT_TRUE(FellGclk(/*prev_lsb=*/0b01, /*cur_lsb=*/0b10));   // LSB 1 -> 0
  EXPECT_TRUE(RisingGclk(/*cur_lsb=*/0b100, /*next_lsb=*/0b101));
  EXPECT_TRUE(FallingGclk(/*cur_lsb=*/0b011, /*next_lsb=*/0b010));
}

// §16.9.4: $changed_gclk/$stable_gclk compare the whole expression value, so a
// change in any bit registers as changed and not stable.
TEST(GlobalClockingSampledValue, StableComparesWholeValue) {
  EXPECT_FALSE(StableGclk(/*prev_value=*/0b10,
                          /*cur_value=*/0b00));  // upper bit changed
  EXPECT_TRUE(ChangedGclk(/*prev_value=*/0b10, /*cur_value=*/0b00));
}

// §16.9.4: the evaluator tolerates a global clocking function written with no
// argument, yielding a defined zero rather than misbehaving.
TEST(GlobalClockingSampledValue, EvalWithMissingArgumentIsDefined) {
  SysTaskFixture f;
  auto* past = MkSysCall(f.arena, "$past_gclk", {});
  EXPECT_EQ(EvalExpr(past, f.ctx, f.arena).ToUint64(), 0u);
}

}  // namespace
