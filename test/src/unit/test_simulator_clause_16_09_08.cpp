// §16.9.8: First_match operation

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

TEST(SvaEngine, SequenceOperatorIntersect) {
  // Intersect: both match and complete at the same cycle.
  EXPECT_TRUE(EvalSequenceIntersect(true, true, 3, 3));
  // Different lengths: false.
  EXPECT_FALSE(EvalSequenceIntersect(true, true, 3, 4));
  EXPECT_FALSE(EvalSequenceIntersect(true, false, 3, 3));
}

} // namespace
