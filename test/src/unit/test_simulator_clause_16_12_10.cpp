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

// §16.12.10: weak `nexttime property_expr` holds when property_expr holds at
// the next clock tick. With the target tick reachable, the nexttime verdict is
// the inner property_expr's verdict at that tick.
TEST(SvaEngine, WeakNexttimeTakesInnerVerdictAtNextTick) {
  EXPECT_EQ(EvalNexttime(/*strong=*/false, /*target_tick_reachable=*/true,
                         PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalNexttime(/*strong=*/false, /*target_tick_reachable=*/true,
                         PropertyResult::kFail),
            PropertyResult::kFail);
}

// §16.12.10: weak nexttime also holds when there is no further clock tick — the
// clock ran out before the obligation could be disproven.
TEST(SvaEngine, WeakNexttimePassesWhenNoFurtherTick) {
  EXPECT_EQ(EvalNexttime(/*strong=*/false, /*target_tick_reachable=*/false,
                         PropertyResult::kFail),
            PropertyResult::kPass);
}

// §16.12.10: strong `s_nexttime property_expr` requires the next clock tick to
// exist and property_expr to hold there; a reachable tick yields the inner
// verdict.
TEST(SvaEngine, StrongNexttimeTakesInnerVerdictAtNextTick) {
  EXPECT_EQ(EvalNexttime(/*strong=*/true, /*target_tick_reachable=*/true,
                         PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalNexttime(/*strong=*/true, /*target_tick_reachable=*/true,
                         PropertyResult::kFail),
            PropertyResult::kFail);
}

// §16.12.10: strong nexttime fails when the required next tick never arrives —
// the dual of the weak form's pass in the same situation.
TEST(SvaEngine, StrongNexttimeFailsWhenNoFurtherTick) {
  EXPECT_EQ(EvalNexttime(/*strong=*/true, /*target_tick_reachable=*/false,
                         PropertyResult::kPass),
            PropertyResult::kFail);
}

// §16.12.10: the index counts clock ticks with counting starting at the current
// time step, so the target for index n is reachable exactly when n further
// ticks exist after the current step.
TEST(SvaEngine, NexttimeIndexCountsFromCurrentStep) {
  EXPECT_TRUE(NexttimeTargetReachable(/*index=*/2, /*future_clock_ticks=*/2));
  EXPECT_TRUE(NexttimeTargetReachable(/*index=*/2, /*future_clock_ticks=*/3));
  EXPECT_FALSE(NexttimeTargetReachable(/*index=*/2, /*future_clock_ticks=*/1));
}

// §16.12.10: nexttime[0] and s_nexttime[0] target the current step and act as
// pure alignment operators — the target is reachable even with no further tick.
TEST(SvaEngine, NexttimeZeroIndexIsAlignmentOperator) {
  EXPECT_TRUE(NexttimeTargetReachable(/*index=*/0, /*future_clock_ticks=*/0));
  EXPECT_TRUE(NexttimeTargetReachable(/*index=*/0, /*future_clock_ticks=*/5));
}

// §16.12.10: the non-indexed nexttime/s_nexttime forms target the next clock
// tick, i.e. index 1. At that boundary the index-1 target is reachable exactly
// when one further tick exists, so a missing further tick leaves it out of
// reach — the reachability input behind the weak-pass / strong-fail next-tick
// cases.
TEST(SvaEngine, NexttimeIndexOneMatchesNextTick) {
  EXPECT_TRUE(NexttimeTargetReachable(/*index=*/1, /*future_clock_ticks=*/1));
  EXPECT_TRUE(NexttimeTargetReachable(/*index=*/1, /*future_clock_ticks=*/4));
  EXPECT_FALSE(NexttimeTargetReachable(/*index=*/1, /*future_clock_ticks=*/0));
}

// §16.12.10: composing the two helpers reproduces the indexed-form semantics.
// Indexed weak nexttime holds when the indexed tick is out of reach ("there are
// not n clock ticks") and otherwise takes the inner verdict; indexed strong
// nexttime instead fails when the indexed tick is out of reach.
TEST(SvaEngine, IndexedNexttimeComposesReachabilityWithStrength) {
  // Index 3 needs three further ticks but only one is available: out of reach.
  bool reachable =
      NexttimeTargetReachable(/*index=*/3, /*future_clock_ticks=*/1);
  EXPECT_EQ(EvalNexttime(/*strong=*/false, reachable, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalNexttime(/*strong=*/true, reachable, PropertyResult::kPass),
            PropertyResult::kFail);

  // Index 3 with three further ticks available: in reach, so the inner verdict
  // governs both the weak and the strong reading.
  reachable = NexttimeTargetReachable(/*index=*/3, /*future_clock_ticks=*/3);
  EXPECT_EQ(EvalNexttime(/*strong=*/false, reachable, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalNexttime(/*strong=*/true, reachable, PropertyResult::kFail),
            PropertyResult::kFail);
}

// §16.12.10: when the target tick is reachable the nexttime verdict is exactly
// the property_expr's verdict at that tick — the weak/strong distinction only
// governs the unreachable case. A property_expr can itself evaluate vacuously
// (for example an inner implication whose antecedent does not match at the
// target tick), and that vacuous pass must flow through the nexttime unchanged
// under both readings rather than being reclassified as a plain pass.
TEST(SvaEngine, ReachableNexttimePassesInnerVacuousVerdictThrough) {
  EXPECT_EQ(EvalNexttime(/*strong=*/false, /*target_tick_reachable=*/true,
                         PropertyResult::kVacuousPass),
            PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalNexttime(/*strong=*/true, /*target_tick_reachable=*/true,
                         PropertyResult::kVacuousPass),
            PropertyResult::kVacuousPass);
}

}  // namespace
