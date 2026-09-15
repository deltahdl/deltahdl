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
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"
#include "simulator/variable.h"

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
  EXPECT_TRUE(MatchEmptyOrNonempty(0, /*empty_case_match=*/true,
                                   /*nonempty_case_match=*/false));
  EXPECT_TRUE(MatchEmptyOrNonempty(0, /*empty_case_match=*/false,
                                   /*nonempty_case_match=*/true));
  EXPECT_FALSE(MatchEmptyOrNonempty(0, /*empty_case_match=*/false,
                                    /*nonempty_case_match=*/false));

  EXPECT_FALSE(MatchEmptyOrNonempty(1, /*empty_case_match=*/true,
                                    /*nonempty_case_match=*/false));
  EXPECT_TRUE(MatchEmptyOrNonempty(1, /*empty_case_match=*/false,
                                   /*nonempty_case_match=*/true));
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
  EXPECT_TRUE(MatchEmptyOrNonempty(0, /*empty_case_match=*/true,
                                   /*nonempty_case_match=*/true));
}

// §16.9.2.1 edge case for (empty ##n seq), n>0, the mirror of the right-side
// minimal-delay case: at n=1 the carried delay collapses to 0, yet the left
// rule reduces to (##0 seq) and — unlike (seq ##n empty) — appends no trailing
// `true. This same collapse of a written ##1 down to an effective ##0 is why
// matching the empty case a[*0] costs one clock tick less than the length-1
// case a[*1] would. Pinning append_true==false at the boundary where the delay
// vanishes keeps the (empty ##n seq)/(seq ##n empty) asymmetry from silently
// degrading into the right-side form once effective_delay reaches its minimum.
TEST(SvaEngine, EmptyConcatLeftMinimalDelayDoesNotAppendTrue) {
  EmptyConcatResult r = ConcatEmptyMatch(EmptyConcatSide::kEmptyLeft, 1);
  EXPECT_TRUE(r.matchable);
  EXPECT_EQ(r.effective_delay, 0u);
  EXPECT_FALSE(r.append_true);
}

// --- Live cases: the linear sequence monitor over real source ---

// The source the cases share: clk rises at 5, 15, 25, ...; `drive` writes a,
// b and c between the ticks; and a process counts the ticks at which the named
// sequence `rule`, whose body is `body`, reaches its end point, keeping the
// last such time.
std::string EmptyMatchSource(const std::string& body,
                             const std::string& drive) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic a = 0;\n"
         "  logic b = 0;\n"
         "  logic c = 0;\n"
         "  int hits = 0;\n"
         "  int last = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  sequence rule;\n"
         "    @(posedge clk) " +
         body +
         ";\n"
         "  endsequence\n"
         "  initial begin\n" +
         drive +
         "    #40 $finish;\n"
         "  end\n"
         "  initial forever begin\n"
         "    wait (rule.triggered);\n"
         "    hits = hits + 1;\n"
         "    last = $time;\n"
         "    @(posedge clk);\n"
         "  end\n"
         "endmodule\n";
}

// b for the ticks at 15 and 25, a for the tick at 25.
const char* const kBThenAb =
    "    #10 b = 1;\n"
    "    #10 a = 1;\n"
    "    #10 a = 0; b = 0;\n";

// §16.9.2.1: `empty ##0 seq` is no match, so `a[*0] ##0 b` never ends,
// while ``true ##0 b`, the fusion of two sequences of length 1, ends at every
// tick b holds at, 15 and 25.
TEST(EmptyMatchSequences, EmptyBeforeZeroDelayNeverMatches) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(EmptyMatchSource("a[*0] ##0 b", kBThenAb), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 0u);
  SimFixture g;
  auto* fused =
      RunAndFindVar(EmptyMatchSource("1'b1 ##0 b", kBThenAb), g, "hits");
  ASSERT_NE(fused, nullptr);
  EXPECT_EQ(fused->value.ToUint64(), 2u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 25u);
}

// §16.9.2.1: `seq ##n empty` is `seq ##(n-1) `true`, so `b ##2 a[*0]` ends
// one tick after each b, at 25 and 35, and `seq ##0 empty` is no match, so
// `b ##0 a[*0]` never ends.
TEST(EmptyMatchSequences, EmptyAfterADelayCollapsesItByOne) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(EmptyMatchSource("b ##2 a[*0]", kBThenAb), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
  SimFixture g;
  auto* none =
      RunAndFindVar(EmptyMatchSource("b ##0 a[*0]", kBThenAb), g, "hits");
  ASSERT_NE(none, nullptr);
  EXPECT_EQ(none->value.ToUint64(), 0u);
}

// §16.9.2.1: a sequence admitting empty and nonempty matches is the or of
// its cases, `b ##1 a[*0:1] ##2 c` being `(b ##2 c) or (b ##1 a ##2 c)`: with
// b at 15 and c at 35 it ends at 35 by the empty case, and with b at 45, a at
// 55 and c at 75 it ends at 75 by the other; the or written out ends alike.
TEST(EmptyMatchSequences, RangeAdmittingEmptyIsTheOrOfItsCases) {
  const char* const kTwoRounds =
      "    #10 b = 1;\n"
      "    #10 b = 0;\n"
      "    #10 c = 1;\n"
      "    #10 c = 0; b = 1;\n"
      "    #10 b = 0; a = 1;\n"
      "    #10 a = 0;\n"
      "    #10 c = 1;\n"
      "    #10 c = 0;\n";
  SimFixture f;
  auto* hits = RunAndFindVar(
      EmptyMatchSource("b ##1 a[*0:1] ##2 c", kTwoRounds), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 75u);
  SimFixture g;
  auto* spelled = RunAndFindVar(
      EmptyMatchSource("b ##2 c or b ##1 a ##2 c", kTwoRounds), g, "hits");
  ASSERT_NE(spelled, nullptr);
  EXPECT_EQ(spelled->value.ToUint64(), 2u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 75u);
}

}  // namespace
