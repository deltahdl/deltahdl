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

// §16.12.7: for the overlapped form (|->) the consequent is evaluated at the
// end point of the antecedent match, so a matched antecedent yields exactly the
// consequent's verdict. With no antecedent match the implication holds
// vacuously.
TEST(SvaEngine, OverlappingImplication) {
  EXPECT_EQ(EvalImplication(true, true, false), PropertyResult::kPass);
  EXPECT_EQ(EvalImplication(true, false, false), PropertyResult::kFail);

  EXPECT_EQ(EvalImplication(false, false, false), PropertyResult::kVacuousPass);
}

// §16.12.7: for the nonoverlapped form (|=>) the consequent starts one clock
// tick after the antecedent match, so a matched antecedent defers its verdict
// rather than resolving immediately. With no antecedent match the implication
// still holds vacuously.
TEST(SvaEngine, NonOverlappingImplication) {
  EXPECT_EQ(EvalImplication(true, true, true), PropertyResult::kPending);
  EXPECT_EQ(EvalImplication(false, false, true), PropertyResult::kVacuousPass);
}

// §16.12.7: a deferred nonoverlapped implication is settled at the next tick;
// when the consequent then holds, the overall implication passes.
TEST(SvaEngine, PropertyPendingResolvesPass) {
  auto r1 = EvalImplication(true, false, true);
  EXPECT_EQ(r1, PropertyResult::kPending);

  auto resolved = ResolveNonOverlapping(true);
  EXPECT_EQ(resolved, PropertyResult::kPass);
}

// §16.12.7: a deferred nonoverlapped implication is settled at the next tick;
// when the consequent fails there, the overall implication fails.
TEST(SvaEngine, PropertyPendingResolvesFail) {
  auto r1 = EvalImplication(true, false, true);
  EXPECT_EQ(r1, PropertyResult::kPending);

  auto resolved = ResolveNonOverlapping(false);
  EXPECT_EQ(resolved, PropertyResult::kFail);
}

// §16.12.7 edge case: with no antecedent match the implication holds vacuously,
// and that verdict is independent of the consequent — a consequent that would
// itself hold does not promote the vacuous hold to an ordinary pass, in either
// the overlapped or the nonoverlapped form. This exercises the antecedent
// short-circuit in EvalImplication, which returns before the consequent or the
// overlap flag are consulted.
TEST(SvaEngine, NoAntecedentMatchHoldsVacuouslyRegardlessOfConsequent) {
  EXPECT_EQ(EvalImplication(false, true, false), PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalImplication(false, true, true), PropertyResult::kVacuousPass);
}

}  // namespace
