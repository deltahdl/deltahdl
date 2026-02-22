// §16.15: Disable iff resolution

#include <gtest/gtest.h>
#include <cstdint>
#include <string_view>
#include <vector>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/sva_engine.h"

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
// Concurrent assertion disable iff (section 16.12.5)
// =============================================================================
TEST(SvaEngine, DisableIffTrue) {
  // When disable condition is true, assertion is vacuously passed.
  PropertyResult result = EvalWithDisableIff(true, PropertyResult::kFail);
  EXPECT_EQ(result, PropertyResult::kVacuousPass);
}

TEST(SvaEngine, DisableIffFalse) {
  // When disable condition is false, assertion result is unchanged.
  PropertyResult result = EvalWithDisableIff(false, PropertyResult::kFail);
  EXPECT_EQ(result, PropertyResult::kFail);
}

TEST(SvaEngine, DisableIffFalsePass) {
  PropertyResult result = EvalWithDisableIff(false, PropertyResult::kPass);
  EXPECT_EQ(result, PropertyResult::kPass);
}

}  // namespace
