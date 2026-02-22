// §16.9.4: Global clocking past and future sampled value functions

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
// Goto repetition [->N] (section 16.9.4)
// =============================================================================
TEST(SvaEngine, GotoRepetition) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kGotoRepetition;
  seq.rep_min = 2;
  seq.rep_max = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  // Two non-consecutive matches: 0,1,0,1.
  // Goto: match must end at the Nth match.
  EXPECT_TRUE(MatchGotoRepetition(seq, {0, 1, 0, 1}));
  // Only one match.
  EXPECT_FALSE(MatchGotoRepetition(seq, {0, 1, 0, 0}));
}

TEST(SvaEngine, GotoRepetitionEndsAtMatch) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kGotoRepetition;
  seq.rep_min = 1;
  seq.rep_max = 1;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  // Last element must be a match for goto repetition.
  EXPECT_TRUE(MatchGotoRepetition(seq, {0, 0, 1}));
  EXPECT_FALSE(MatchGotoRepetition(seq, {0, 1, 0}));
}

}  // namespace
