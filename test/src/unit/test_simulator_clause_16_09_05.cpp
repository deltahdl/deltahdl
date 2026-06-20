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

TEST(SvaEngine, NonConsecutiveRepetition) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kNonConsecutiveRepetition;
  seq.rep_min = 2;
  seq.rep_max = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchNonConsecutiveRepetition(seq, {0, 1, 0, 1, 0}));
  EXPECT_TRUE(MatchNonConsecutiveRepetition(seq, {1, 0, 1}));
  EXPECT_FALSE(MatchNonConsecutiveRepetition(seq, {1, 0, 0}));
}

// §16.9.5: the `and` of two operands matches only when both operands match.
// When the operands are sampled (Boolean) expressions, the composite is true
// exactly when both evaluate true.
TEST(SvaEngine, AndRequiresBothOperandsToMatch) {
  EXPECT_TRUE(EvalSequenceAnd(true, true));
  EXPECT_FALSE(EvalSequenceAnd(true, false));
  EXPECT_FALSE(EvalSequenceAnd(false, true));
  EXPECT_FALSE(EvalSequenceAnd(false, false));
}

// §16.9.5: the operands begin at the same time but may finish at different
// times; the composite match completes at the later of the two end times.
TEST(SvaEngine, AndEndTimeIsTheLaterOperandEndTime) {
  // Mirrors (te1 ##2 te2) and (te3 ##2 te4 ##2 te5): operand ends at ticks 10
  // and 12, composite completes at the later tick 12.
  SequenceAndMatch m = EvalSequenceAndMatch(true, 10, true, 12);
  EXPECT_TRUE(m.matched);
  EXPECT_EQ(m.end_time, 12u);

  // Order of the operands does not change which end time wins.
  SequenceAndMatch swapped = EvalSequenceAndMatch(true, 12, true, 10);
  EXPECT_TRUE(swapped.matched);
  EXPECT_EQ(swapped.end_time, 12u);

  // Boolean operands share a single tick, so the composite ends there.
  SequenceAndMatch boolean = EvalSequenceAndMatch(true, 1, true, 1);
  EXPECT_TRUE(boolean.matched);
  EXPECT_EQ(boolean.end_time, 1u);

  // No composite match unless both operands match.
  EXPECT_FALSE(EvalSequenceAndMatch(true, 10, false, 12).matched);
  EXPECT_FALSE(EvalSequenceAndMatch(false, 10, true, 12).matched);
}

}  // namespace
