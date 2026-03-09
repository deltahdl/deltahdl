#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"

using namespace delta;

struct SvaFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

namespace {

TEST(SvaEngine, GotoRepetition) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kGotoRepetition;
  seq.rep_min = 2;
  seq.rep_max = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchGotoRepetition(seq, {0, 1, 0, 1}));

  EXPECT_FALSE(MatchGotoRepetition(seq, {0, 1, 0, 0}));
}

TEST(SvaEngine, GotoRepetitionEndsAtMatch) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kGotoRepetition;
  seq.rep_min = 1;
  seq.rep_max = 1;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchGotoRepetition(seq, {0, 0, 1}));
  EXPECT_FALSE(MatchGotoRepetition(seq, {0, 1, 0}));
}

}  // namespace
