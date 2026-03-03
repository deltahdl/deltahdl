// §16.9.2: Repetition in sequences

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

// =============================================================================
// Sequence repetition [*N] (section 16.9.2)
// =============================================================================
TEST(SvaEngine, ConsecutiveRepetitionExact) {
  SvaFixture f;
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 3;
  seq.rep_max = 3;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  // Simulate 3 consecutive matches.
  auto result = MatchRepetition(seq, {1, 1, 1});
  EXPECT_TRUE(result);
}

}  // namespace
