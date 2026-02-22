// §16.9.1: Operator precedence

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
// Sequence delay ##N (section 16.9)
// =============================================================================
TEST(SvaEngine, SequenceDelaySimple) {
  SvaFixture f;
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kDelay;
  seq.delay_cycles = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  SequenceAttempt sa;
  sa.delay_remaining = 2;
  AdvanceSequence(sa);
  AdvanceSequence(sa);
  EXPECT_EQ(sa.delay_remaining, 0u);
}

TEST(SvaEngine, SequenceDelayZero) {
  SequenceAttempt sa;
  sa.delay_remaining = 0;
  AdvanceSequence(sa);
  // Zero delay: still at 0.
  EXPECT_EQ(sa.delay_remaining, 0u);
}

// =============================================================================
// Sequence matching complete patterns
// =============================================================================
TEST(SvaEngine, DelaySequenceMatchFull) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kDelay;
  seq.delay_cycles = 2;
  seq.expr_check = [](uint64_t v) { return v != 0; };

  // Values: cycle0=1, delay 2, cycle2 check.
  std::vector<uint64_t> vals = {1, 0, 1};
  EXPECT_TRUE(MatchDelaySequence(seq, vals));
}

TEST(SvaEngine, DelaySequenceNoMatchAtEnd) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kDelay;
  seq.delay_cycles = 1;
  seq.expr_check = [](uint64_t v) { return v != 0; };

  std::vector<uint64_t> vals = {1, 0};
  EXPECT_FALSE(MatchDelaySequence(seq, vals));
}

}  // namespace
