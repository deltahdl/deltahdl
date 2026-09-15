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

// --- Live cases: the linear sequence monitor over real source ---

// The source the cases share: clk rises at 5, 15, 25, ...; `drive` writes a,
// b and c between the ticks; and a process counts the ticks at which the named
// sequence `rule`, whose body is `body`, reaches its end point, keeping the
// last such time.
std::string RepetitionSource(const std::string& body,
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

// a for the tick at 15, b for the ticks at 25, 35 and 45, c for the tick at
// 55.
const char* const kThreeBs =
    "    #10 a = 1;\n"
    "    #10 a = 0; b = 1;\n"
    "    #30 b = 0; c = 1;\n"
    "    #10 c = 0;\n";

// §16.9.2: `b[*3]` is three consecutive matches of b, so `a ##1 b[*3] ##1 c`
// is `a ##1 b ##1 b ##1 b ##1 c`, ending at 55 over the three b's; with b at
// two ticks alone it does not end.
TEST(SequenceRepetition, ConsecutiveRepetitionByExactCount) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(RepetitionSource("a ##1 b[*3] ##1 c", kThreeBs), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
  SimFixture g;
  auto* none = RunAndFindVar(RepetitionSource("a ##1 b[*3] ##1 c",
                                              "    #10 a = 1;\n"
                                              "    #10 a = 0; b = 1;\n"
                                              "    #20 b = 0; c = 1;\n"
                                              "    #10 c = 0;\n"),
                             g, "hits");
  ASSERT_NE(none, nullptr);
  EXPECT_EQ(none->value.ToUint64(), 0u);
}

// §16.9.2: `a ##1 b[*1:$] ##1 c` matches over three or more ticks with a at
// the first, c at the last and b at every tick strictly between: over the
// three b's it ends at 55 alone, c being low before.
TEST(SequenceRepetition, UnboundedConsecutiveRepetitionFillsTheMiddle) {
  SimFixture f;
  auto* hits = RunAndFindVar(RepetitionSource("a ##1 b[*1:$] ##1 c", kThreeBs),
                             f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
}

// §16.9.2 and §16.9.2.1: `a[*0:3] ##1 b ##1 c` admits an empty match of a,
// `empty ##1 b` being `b`, so with a never high it ends at 25 over b at 15
// and c at 25; with a high at 15 and 25 it ends at 45 over b at 35 and c at
// 45.
TEST(SequenceRepetition, RangeFromZeroAdmitsAnEmptyMatch) {
  SimFixture f;
  auto* hits = RunAndFindVar(RepetitionSource("a[*0:3] ##1 b ##1 c",
                                              "    #10 b = 1;\n"
                                              "    #10 b = 0; c = 1;\n"
                                              "    #10 c = 0;\n"),
                             f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 25u);
  SimFixture g;
  auto* two = RunAndFindVar(RepetitionSource("a[*0:3] ##1 b ##1 c",
                                             "    #10 a = 1;\n"
                                             "    #20 a = 0; b = 1;\n"
                                             "    #10 b = 0; c = 1;\n"
                                             "    #10 c = 0;\n"),
                            g, "hits");
  ASSERT_NE(two, nullptr);
  EXPECT_EQ(two->value.ToUint64(), 1u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 45u);
}

// a for the tick at 15, b for the ticks at 25 and 45, c for the tick at 55.
const char* const kTwoBsApart =
    "    #10 a = 1;\n"
    "    #10 a = 0; b = 1;\n"
    "    #10 b = 0;\n"
    "    #10 b = 1;\n"
    "    #10 b = 0; c = 1;\n"
    "    #10 c = 0;\n";

// §16.9.2: goto repetition `b[->2:3]` matches b at two or three ticks that
// need not be consecutive and ends at the last of them, so `a ##1 b[->2:3]
// ##1 c` ends at 55 with b at 25 and 45 and c at 55.
TEST(SequenceRepetition, GotoRepetitionEndsAtTheLastMatch) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      RepetitionSource("a ##1 b[->2:3] ##1 c", kTwoBsApart), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
}

// §16.9.2: nonconsecutive repetition `b[=2:3]` is the goto form extended by
// ticks b is false at, so with b at 25 and 35 and c at 55, where the goto
// form needs c at 45, `a ##1 b[=2:3] ##1 c` ends at 55 and the goto form
// never.
TEST(SequenceRepetition, NonconsecutiveRepetitionExtendsPastTheLastMatch) {
  const char* const two_then_gap =
      "    #10 a = 1;\n"
      "    #10 a = 0; b = 1;\n"
      "    #20 b = 0;\n"
      "    #10 c = 1;\n"
      "    #10 c = 0;\n";
  SimFixture f;
  auto* hits = RunAndFindVar(
      RepetitionSource("a ##1 b[=2:3] ##1 c", two_then_gap), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
  SimFixture g;
  auto* goto_hits = RunAndFindVar(
      RepetitionSource("a ##1 b[->2:3] ##1 c", two_then_gap), g, "hits");
  ASSERT_NE(goto_hits, nullptr);
  EXPECT_EQ(goto_hits->value.ToUint64(), 0u);
}

// §16.9.2: consecutive repetition of a sequence, `(a ##2 b)[*3]`, is the
// sequence three times over with a tick between, `(a ##2 b) ##1 (a ##2 b) ##1
// (a ##2 b)`, ending at 95 over a at 15, 45 and 75 and b at 35, 65 and 95.
TEST(SequenceRepetition, ConsecutiveRepetitionOfASequenceUnrolls) {
  SimFixture f;
  auto* hits = RunAndFindVar(RepetitionSource("(a ##2 b)[*3]",
                                              "    #10 a = 1;\n"
                                              "    #10 a = 0;\n"
                                              "    #10 b = 1;\n"
                                              "    #10 b = 0; a = 1;\n"
                                              "    #10 a = 0;\n"
                                              "    #10 b = 1;\n"
                                              "    #10 b = 0; a = 1;\n"
                                              "    #10 a = 0;\n"
                                              "    #10 b = 1;\n"
                                              "    #10 b = 0;\n"),
                             f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 95u);
}

}  // namespace
