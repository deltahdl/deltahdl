#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_sequence_ticks.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine_queues.h"
#include "simulator/sva_engine_sequences.h"

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

// §16.9.5: negative form of the both-match requirement for the match/end-time
// variant. When neither operand matches there is no composite match, closing
// the enumeration alongside the two single-operand-fail cases above.
TEST(SvaEngine, AndFailsWhenNeitherOperandMatches) {
  EXPECT_FALSE(EvalSequenceAndMatch(false, 10, false, 12).matched);
}

// --- Live cases: the linear sequence monitor over real source ---

// §16.9.5, Figure 16-5: te1 at ticks 1, 2 and 8; te2 at 10 and 12; te3 at 2,
// 3 and 8; te4 at 4 and 10; te5 at 6 and 12. The operands begin at the same
// tick: at 8, te1 ##2 te2 ends at 10 and te3 ##2 te4 ##2 te5 at 12, so the
// composite ends at the later of them, 12, which is the tick at 115.
TEST(SequenceAnd, EndsWhereTheLaterOperandEnds) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource(
          "(te1 ##2 te2) and (te3 ##2 te4 ##2 te5)",
          DriveTicks({{1, 2, 8}, {10, 12}, {2, 3, 8}, {4, 10}, {6, 12}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 115u);
}

// §16.9.5, Figure 16-6: with te2 at 9 to 13, te1 ##[1:5] te2 has five matches
// from tick 8, ending at 9 to 13, and each is combined with the one match of
// te3 ##2 te4 ##2 te5 ending at 12: four composite matches end at 12 and the
// fifth at 13, so the end point is reached at the ticks at 115 and 125.
TEST(SequenceAnd, RangeOperandEndsAtEachLaterTick) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource(
          "(te1 ##[1:5] te2) and (te3 ##2 te4 ##2 te5)",
          DriveTicks(
              {{1, 2, 8}, {9, 10, 11, 12, 13}, {2, 3, 8}, {4, 10}, {6, 12}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 125u);
}

// §16.9.5: both operands must match. With te3, te4 and te5 never high the
// first operand's match from 8 stands alone, and with te2 never high the
// second's does; neither is a match of the composite.
TEST(SequenceAnd, OneOperandMatchingAloneIsNoMatch) {
  const std::string kBody = "(te1 ##2 te2) and (te3 ##2 te4 ##2 te5)";
  SimFixture f;
  auto* first_alone = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{1, 2, 8}, {10, 12}, {}, {}, {}})),
      f, "hits");
  ASSERT_NE(first_alone, nullptr);
  EXPECT_EQ(first_alone->value.ToUint64(), 0u);
  SimFixture g;
  auto* second_alone = RunAndFindVar(
      SequenceTickSource(
          kBody, DriveTicks({{1, 2, 8}, {}, {2, 3, 8}, {4, 10}, {6, 12}})),
      g, "hits");
  ASSERT_NE(second_alone, nullptr);
  EXPECT_EQ(second_alone->value.ToUint64(), 0u);
}

// §16.9.5, Figure 16-7: with sampled expressions as operands, te1 and te2
// matches at the ticks both are true, 1, 3, 8 and 14, and at no other, so the
// end point is reached four times, last at the tick at 135.
TEST(SequenceAnd, BooleanOperandsMatchWhereBothHold) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource(
          "te1 and te2",
          DriveTicks({{1, 3, 8, 14}, {1, 3, 5, 8, 9, 14}, {}, {}, {}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 135u);
}

}  // namespace
