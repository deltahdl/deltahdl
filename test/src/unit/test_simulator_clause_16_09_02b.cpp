// §16.9.2: Repetition in sequences

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

TEST(SvaEngine, ConsecutiveRepetitionNotEnough) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 3;
  seq.rep_max = 3;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  // Only 2 matches before a mismatch.
  auto result = MatchRepetition(seq, {1, 1, 0});
  EXPECT_FALSE(result);
}

TEST(SvaEngine, ConsecutiveRepetitionRange) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 2;
  seq.rep_max = 4;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  // 2 is within [2:4].
  EXPECT_TRUE(MatchRepetition(seq, {1, 1}));
  // 3 is within [2:4].
  EXPECT_TRUE(MatchRepetition(seq, {1, 1, 1}));
  // 4 is within [2:4].
  EXPECT_TRUE(MatchRepetition(seq, {1, 1, 1, 1}));
  // 1 is below range.
  EXPECT_FALSE(MatchRepetition(seq, {1}));
}

// =============================================================================
// Edge cases and robustness
// =============================================================================
TEST(SvaEngine, RepetitionZeroMin) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 0;
  seq.rep_max = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  // Zero matches is valid when min is 0.
  EXPECT_TRUE(MatchRepetition(seq, {}));
  EXPECT_TRUE(MatchRepetition(seq, {1}));
  EXPECT_TRUE(MatchRepetition(seq, {1, 1}));
}

}  // namespace
