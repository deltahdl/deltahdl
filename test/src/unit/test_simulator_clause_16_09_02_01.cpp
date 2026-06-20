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

// §16.9.2.1: using 0 as a sequence repetition number yields an empty sequence
// (see §16.7), as in a[*0] — the zero-iteration case matches over no ticks.
TEST(SvaEngine, RepetitionZeroMin) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 0;
  seq.rep_max = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchRepetition(seq, {}));
  EXPECT_TRUE(MatchRepetition(seq, {1}));
  EXPECT_TRUE(MatchRepetition(seq, {1, 1}));
}

// §16.9.2.1: (empty ##0 seq) does not result in a match.
TEST(SvaEngine, EmptyConcatZeroDelayLeftNoMatch) {
  EmptyConcatResult r = ConcatEmptyMatch(EmptyConcatSide::kEmptyLeft, 0);
  EXPECT_FALSE(r.matchable);
}

// §16.9.2.1: (seq ##0 empty) does not result in a match.
TEST(SvaEngine, EmptyConcatZeroDelayRightNoMatch) {
  EmptyConcatResult r = ConcatEmptyMatch(EmptyConcatSide::kEmptyRight, 0);
  EXPECT_FALSE(r.matchable);
}

// §16.9.2.1: (empty ##n seq), n>0, is equivalent to (##(n-1) seq) — the empty
// operand collapses, reducing the delay by one with no trailing `true.
TEST(SvaEngine, EmptyConcatLeftCollapsesDelay) {
  EmptyConcatResult r = ConcatEmptyMatch(EmptyConcatSide::kEmptyLeft, 2);
  EXPECT_TRUE(r.matchable);
  EXPECT_EQ(r.effective_delay, 1u);
  EXPECT_FALSE(r.append_true);
}

// §16.9.2.1: (seq ##n empty), n>0, is equivalent to (seq ##(n-1) `true) — the
// delay reduces by one and a trailing `true extends the match past seq.
TEST(SvaEngine, EmptyConcatRightCollapsesDelayWithTrue) {
  EmptyConcatResult r = ConcatEmptyMatch(EmptyConcatSide::kEmptyRight, 2);
  EXPECT_TRUE(r.matchable);
  EXPECT_EQ(r.effective_delay, 1u);
  EXPECT_TRUE(r.append_true);
}

// §16.9.2.1: matching the 0-tick empty case a[*0] runs one tick shorter than
// the 1-tick case a[*1]; concatenating across a[*0] ##1 b collapses to ##0 b,
// one fewer tick than a[*1] ##1 b would spend.
TEST(SvaEngine, EmptyCaseExecutionOneTickShorter) {
  EmptyConcatResult empty = ConcatEmptyMatch(EmptyConcatSide::kEmptyLeft, 1);
  EXPECT_TRUE(empty.matchable);
  EXPECT_EQ(empty.effective_delay, 0u);
}

// §16.9.2.1: a[*0] ##0 b can never match (empty at zero delay), whereas the
// fusion `true ##0 b matches whenever b holds. The latter is an ordinary
// zero-delay match of b.
TEST(SvaEngine, EmptyAtZeroDelayNeverMatchesButFusionDoes) {
  EXPECT_FALSE(ConcatEmptyMatch(EmptyConcatSide::kEmptyRight, 0).matchable);

  SvaSequence b;
  b.kind = SvaSequenceKind::kDelay;
  b.delay_cycles = 0;
  b.expr_check = [](uint64_t v) { return v == 1; };
  EXPECT_TRUE(MatchDelaySequence(b, {1}));
  EXPECT_FALSE(MatchDelaySequence(b, {0}));
}

// §16.9.2.1: a repetition admitting both empty and nonempty matches (a[*0:1])
// is evaluated as the OR of its empty and nonempty cases; a range that excludes
// zero (a[*1:2]) keeps only the nonempty case.
TEST(SvaEngine, RangeAdmittingEmptyIsOrOfCases) {
  EXPECT_TRUE(MatchEmptyOrNonempty(0, /*empty=*/true, /*nonempty=*/false));
  EXPECT_TRUE(MatchEmptyOrNonempty(0, /*empty=*/false, /*nonempty=*/true));
  EXPECT_FALSE(MatchEmptyOrNonempty(0, /*empty=*/false, /*nonempty=*/false));

  EXPECT_FALSE(MatchEmptyOrNonempty(1, /*empty=*/true, /*nonempty=*/false));
  EXPECT_TRUE(MatchEmptyOrNonempty(1, /*empty=*/false, /*nonempty=*/true));
}

// §16.9.2.1 edge case for (seq ##n empty), n>0: at the minimal positive delay
// n=1 the carried delay reduces to 0, yet the rule still trails the surviving
// sequence with `true (seq ##0 `true), so the match extends one tick past seq.
TEST(SvaEngine, EmptyConcatRightMinimalDelayStillAppendsTrue) {
  EmptyConcatResult r = ConcatEmptyMatch(EmptyConcatSide::kEmptyRight, 1);
  EXPECT_TRUE(r.matchable);
  EXPECT_EQ(r.effective_delay, 0u);
  EXPECT_TRUE(r.append_true);
}

// §16.9.2.1 edge case for the empty/nonempty OR-rewrite: when a zero-admitting
// range yields a match under both its empty and nonempty interpretations, the
// disjunction still matches.
TEST(SvaEngine, RangeAdmittingEmptyBothCasesMatch) {
  EXPECT_TRUE(MatchEmptyOrNonempty(0, /*empty=*/true, /*nonempty=*/true));
}

}  // namespace
