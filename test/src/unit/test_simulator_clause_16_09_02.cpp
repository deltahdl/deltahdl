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

TEST(SvaEngine, ConsecutiveRepetitionExact) {
  SvaFixture f;
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 3;
  seq.rep_max = 3;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  auto result = MatchRepetition(seq, {1, 1, 1});
  EXPECT_TRUE(result);
}

TEST(SvaEngine, ConsecutiveRepetitionNotEnough) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 3;
  seq.rep_max = 3;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  auto result = MatchRepetition(seq, {1, 1, 0});
  EXPECT_FALSE(result);
}

TEST(SvaEngine, ConsecutiveRepetitionRange) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 2;
  seq.rep_max = 4;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchRepetition(seq, {1, 1}));

  EXPECT_TRUE(MatchRepetition(seq, {1, 1, 1}));

  EXPECT_TRUE(MatchRepetition(seq, {1, 1, 1, 1}));

  EXPECT_FALSE(MatchRepetition(seq, {1}));
}

// §16.9.2: an exact consecutive count is a single number, so more matches
// than that count is not a match of [*n] — the over-count negative form of
// the exact-count rule.
TEST(SvaEngine, ConsecutiveRepetitionExactRejectsTooMany) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 3;
  seq.rep_max = 3;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_FALSE(MatchRepetition(seq, {1, 1, 1, 1}));
}

// §16.9.2: goto repetition also takes a range [->min:max]. Any count of
// operand matches within the range, with the last tick being a match, is a
// match; a count above the range is not.
TEST(SvaEngine, GotoRepetitionRange) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kGotoRepetition;
  seq.rep_min = 1;
  seq.rep_max = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchGotoRepetition(seq, {1}));
  EXPECT_TRUE(MatchGotoRepetition(seq, {1, 0, 1}));
  EXPECT_FALSE(MatchGotoRepetition(seq, {1, 0, 1, 0, 1}));
}

// §16.9.2: nonconsecutive repetition likewise takes a range [=min:max]. A
// count within the range matches regardless of trailing non-matching ticks;
// a count above the range does not.
TEST(SvaEngine, NonConsecutiveRepetitionRange) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kNonConsecutiveRepetition;
  seq.rep_min = 1;
  seq.rep_max = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchNonConsecutiveRepetition(seq, {1}));
  EXPECT_TRUE(MatchNonConsecutiveRepetition(seq, {1, 0, 1, 0}));
  EXPECT_FALSE(MatchNonConsecutiveRepetition(seq, {1, 0, 1, 0, 1}));
}

// §16.9.2: the repetition maximum may be `$`, a finite but unbounded upper
// bound. With a dollar maximum only the minimum count constrains the match, so
// any number of consecutive matches at or above the minimum is a match while a
// count below the minimum is not. [*2:$] here accepts 2, 3, or more and
// rejects 1.
TEST(SvaEngine, ConsecutiveRepetitionUnboundedMax) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 2;
  seq.rep_max_is_dollar = true;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchRepetition(seq, {1, 1}));
  EXPECT_TRUE(MatchRepetition(seq, {1, 1, 1}));
  EXPECT_TRUE(MatchRepetition(seq, {1, 1, 1, 1, 1, 1}));
  EXPECT_FALSE(MatchRepetition(seq, {1}));
}

// §16.9.2: [*] is [*0:$] — a dollar maximum with a zero minimum, so it matches
// any number of iterations including zero. Modeled here with the unbounded-max
// flag and a zero minimum.
TEST(SvaEngine, ConsecutiveStarShortcutMatchesAnyCount) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 0;
  seq.rep_max_is_dollar = true;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchRepetition(seq, {}));
  EXPECT_TRUE(MatchRepetition(seq, {1, 1, 1}));
}

// §16.9.2: the dollar maximum applies to goto and nonconsecutive repetition
// too — [->min:$] and [=min:$] drop the upper bound while keeping the minimum.
TEST(SvaEngine, GotoAndNonConsecutiveUnboundedMax) {
  SvaSequence go;
  go.kind = SvaSequenceKind::kGotoRepetition;
  go.rep_min = 2;
  go.rep_max_is_dollar = true;
  go.expr_check = [](uint64_t v) { return v == 1; };
  EXPECT_TRUE(MatchGotoRepetition(go, {1, 0, 1, 0, 1}));
  EXPECT_FALSE(MatchGotoRepetition(go, {1}));

  SvaSequence nc;
  nc.kind = SvaSequenceKind::kNonConsecutiveRepetition;
  nc.rep_min = 2;
  nc.rep_max_is_dollar = true;
  nc.expr_check = [](uint64_t v) { return v == 1; };
  EXPECT_TRUE(MatchNonConsecutiveRepetition(nc, {1, 0, 1, 0, 1, 0}));
  EXPECT_FALSE(MatchNonConsecutiveRepetition(nc, {1}));
}

// §16.9.2: goto repetition b[->n] matches finitely many occurrences of the
// Boolean operand and the overall match ends AT the last iterative match — so
// the final observed tick shall itself be a match of the operand.
TEST(SvaEngine, GotoRepetitionEndsOnOperandMatch) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kGotoRepetition;
  seq.rep_min = 2;
  seq.rep_max = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  // Two matches of b, the last tick being a match: the overall match ends here.
  EXPECT_TRUE(MatchGotoRepetition(seq, {1, 0, 1}));

  // Two matches of b, but a trailing non-matching tick means the match does not
  // end at the last iterative match, so goto repetition does not match.
  EXPECT_FALSE(MatchGotoRepetition(seq, {1, 0, 1, 0}));

  // Only one match of b falls short of the required count.
  EXPECT_FALSE(MatchGotoRepetition(seq, {1, 0, 0}));
}

// §16.9.2: nonconsecutive repetition b[=n] is like goto except the overall
// match need not end at the last iterative match — trailing ticks on which the
// operand is false may extend the match. The distinguishing case is exactly the
// trailing-false window that goto repetition rejects.
TEST(SvaEngine, NonConsecutiveRepetitionAllowsTrailingNonMatch) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kNonConsecutiveRepetition;
  seq.rep_min = 2;
  seq.rep_max = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  // Two matches of b with the match ending on a match: accepted, as for goto.
  EXPECT_TRUE(MatchNonConsecutiveRepetition(seq, {1, 0, 1}));

  // Two matches of b followed by a non-matching tick: nonconsecutive repetition
  // still matches, whereas goto repetition would not.
  EXPECT_TRUE(MatchNonConsecutiveRepetition(seq, {1, 0, 1, 0}));
  EXPECT_FALSE(MatchGotoRepetition(seq, {1, 0, 1, 0}));

  // Too few matches of b still fails the count.
  EXPECT_FALSE(MatchNonConsecutiveRepetition(seq, {1, 0, 0}));
}

}  // namespace
