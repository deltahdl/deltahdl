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

// §16.9.6: `intersect` matches only when both operand sequences match. Unlike
// `and`, the operands must additionally share the same end time, i.e. the two
// operand matches must have the same length.
TEST(SvaEngine, IntersectRequiresBothOperandsToMatch) {
  // Equal lengths, both matching: the composite matches.
  EXPECT_TRUE(EvalSequenceIntersect(true, true, 5, 5));

  // A non-matching operand defeats the composite even at equal length.
  EXPECT_FALSE(EvalSequenceIntersect(true, false, 5, 5));
  EXPECT_FALSE(EvalSequenceIntersect(false, true, 5, 5));
  EXPECT_FALSE(EvalSequenceIntersect(false, false, 5, 5));
}

// §16.9.6: the length restriction is the basic difference between `and` and
// `intersect`. When both operands match but their match lengths differ, `and`
// would still match (its end time is the later of the two), whereas `intersect`
// finds no same-length pair and therefore does not match.
TEST(SvaEngine, IntersectRequiresEqualMatchLengths) {
  // Mirrors Figure 16-8 vs Figure 16-6: with operands ending at ticks 12 and
  // 10, `and` matches but `intersect` does not.
  EXPECT_TRUE(EvalSequenceAnd(true, true));
  EXPECT_FALSE(EvalSequenceIntersect(true, true, 4, 6));
  EXPECT_FALSE(EvalSequenceIntersect(true, true, 6, 4));

  // A Boolean-style single-tick pair shares length 1, so intersect matches.
  EXPECT_TRUE(EvalSequenceIntersect(true, true, 1, 1));
}

}  // namespace
