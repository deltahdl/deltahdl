// §16.9.8: First_match operation

#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"

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

}  // namespace
