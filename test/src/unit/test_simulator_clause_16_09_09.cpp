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

// §16.9.9: `exp throughout seq` matches only when the condition holds at every
// clock tick spanned by the sequence match. A single tick where the condition
// is false defeats the whole match, no matter where in the interval it falls.
TEST(SvaEngine, SequenceThroughout) {
  auto check = [](uint64_t v) { return v == 1; };

  // Condition true at every tick: the composite matches.
  std::vector<uint64_t> values = {1, 1, 1, 1};
  EXPECT_TRUE(EvalThroughout(check, values));

  // A false tick in the interior breaks the match.
  values = {1, 1, 0, 1};
  EXPECT_FALSE(EvalThroughout(check, values));

  // The interval boundaries count just as much as the interior: a violation at
  // the first or the last tick is equally fatal. These cases pin the iteration
  // to span the whole interval rather than skipping an end.
  values = {0, 1, 1, 1};
  EXPECT_FALSE(EvalThroughout(check, values));
  values = {1, 1, 1, 0};
  EXPECT_FALSE(EvalThroughout(check, values));

  // A minimal single-tick interval with the condition held still matches.
  values = {1};
  EXPECT_TRUE(EvalThroughout(check, values));
}

// §16.9.9: the construct abbreviates `(exp)[*0:$] intersect seq`, whose `[*0:$]`
// admits a zero-length match. Over an empty interval there is no tick at which
// the condition could fail, so the throughout condition is vacuously held.
TEST(SvaEngine, SequenceThroughoutEmpty) {
  std::vector<uint64_t> values;
  auto check = [](uint64_t v) { return v == 1; };
  EXPECT_TRUE(EvalThroughout(check, values));
}

}
