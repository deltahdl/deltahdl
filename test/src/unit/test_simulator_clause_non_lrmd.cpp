// §non_lrm

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
// SequenceAttempt basics
// =============================================================================
TEST(SvaEngine, SequenceAttemptDefaultState) {
  SequenceAttempt sa;
  EXPECT_EQ(sa.position, 0u);
  EXPECT_EQ(sa.delay_remaining, 0u);
  EXPECT_EQ(sa.match_count, 0u);
  EXPECT_FALSE(sa.completed);
  EXPECT_FALSE(sa.failed);
}

TEST(SvaEngine, SequenceAttemptDelayCountdown) {
  SequenceAttempt sa;
  sa.delay_remaining = 3;
  AdvanceSequence(sa);
  EXPECT_EQ(sa.delay_remaining, 2u);
  EXPECT_FALSE(sa.completed);
  AdvanceSequence(sa);
  EXPECT_EQ(sa.delay_remaining, 1u);
  AdvanceSequence(sa);
  EXPECT_EQ(sa.delay_remaining, 0u);
}

// =============================================================================
// SvaEngine integration tests
// =============================================================================
TEST(SvaEngine, EngineDefaultState) {
  SvaEngine engine;
  EXPECT_EQ(engine.DeferredQueueSize(), 0u);
}

TEST(SvaEngine, FlushClearsQueue) {
  SvaFixture f;

  DeferredAssertion da;
  da.condition_val = 1;
  f.engine.QueueDeferredAssertion(da);
  EXPECT_EQ(f.engine.DeferredQueueSize(), 1u);

  f.engine.FlushDeferredAssertions(f.scheduler, SimTime{0});
  EXPECT_EQ(f.engine.DeferredQueueSize(), 0u);
}

} // namespace
