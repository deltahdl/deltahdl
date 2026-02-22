// §16.12.7: Implication

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/sva_engine.h"
#include <cstdint>
#include <gtest/gtest.h>
#include <string_view>
#include <vector>

using namespace delta;

// =============================================================================
// Test fixture
// =============================================================================
struct SvaFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

namespace {

// =============================================================================
// Property implication |-> and |=> (section 16.12.7)
// =============================================================================
TEST(SvaEngine, OverlappingImplication) {
  // |-> : if antecedent matches, consequent must match at the same cycle.
  EXPECT_EQ(EvalImplication(true, true, false), PropertyResult::kPass);
  EXPECT_EQ(EvalImplication(true, false, false), PropertyResult::kFail);
  // Antecedent false => vacuous pass.
  EXPECT_EQ(EvalImplication(false, false, false), PropertyResult::kVacuousPass);
}

TEST(SvaEngine, NonOverlappingImplication) {
  // |=> : if antecedent matches, consequent is checked on next cycle.
  // When non_overlapping=true and antecedent matches, result is kPending.
  EXPECT_EQ(EvalImplication(true, true, true), PropertyResult::kPending);
  EXPECT_EQ(EvalImplication(false, false, true), PropertyResult::kVacuousPass);
}

TEST(SvaEngine, PropertyPendingResolvesPass) {
  // Simulate |=> with pass on next cycle.
  auto r1 = EvalImplication(true, false, true);
  EXPECT_EQ(r1, PropertyResult::kPending);

  // Next cycle consequent matches.
  auto resolved = ResolveNonOverlapping(true);
  EXPECT_EQ(resolved, PropertyResult::kPass);
}

TEST(SvaEngine, PropertyPendingResolvesFail) {
  auto r1 = EvalImplication(true, false, true);
  EXPECT_EQ(r1, PropertyResult::kPending);

  auto resolved = ResolveNonOverlapping(false);
  EXPECT_EQ(resolved, PropertyResult::kFail);
}

} // namespace
