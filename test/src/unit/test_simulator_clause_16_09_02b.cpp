// Non-LRM tests

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

namespace {

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
