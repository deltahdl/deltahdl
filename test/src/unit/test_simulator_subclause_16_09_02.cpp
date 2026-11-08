#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
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
#include "simulator/sva_engine_queues.h"
#include "simulator/sva_engine_sequences.h"
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

TEST(SvaEngine, ConsecutiveRepetitionExactRejectsTooMany) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 3;
  seq.rep_max = 3;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_FALSE(MatchRepetition(seq, {1, 1, 1, 1}));
}

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

TEST(SvaEngine, ConsecutiveStarShortcutMatchesAnyCount) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kConsecutiveRepetition;
  seq.rep_min = 0;
  seq.rep_max_is_dollar = true;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchRepetition(seq, {}));
  EXPECT_TRUE(MatchRepetition(seq, {1, 1, 1}));
}

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

TEST(SvaEngine, GotoRepetitionEndsOnOperandMatch) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kGotoRepetition;
  seq.rep_min = 2;
  seq.rep_max = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchGotoRepetition(seq, {1, 0, 1}));

  EXPECT_FALSE(MatchGotoRepetition(seq, {1, 0, 1, 0}));

  EXPECT_FALSE(MatchGotoRepetition(seq, {1, 0, 0}));
}

TEST(SvaEngine, NonConsecutiveRepetitionAllowsTrailingNonMatch) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kNonConsecutiveRepetition;
  seq.rep_min = 2;
  seq.rep_max = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchNonConsecutiveRepetition(seq, {1, 0, 1}));

  EXPECT_TRUE(MatchNonConsecutiveRepetition(seq, {1, 0, 1, 0}));
  EXPECT_FALSE(MatchGotoRepetition(seq, {1, 0, 1, 0}));

  EXPECT_FALSE(MatchNonConsecutiveRepetition(seq, {1, 0, 0}));
}

std::string RepetitionSource(const std::string& body,
                             const std::string& drive) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic a = 0;\n"
         "  logic b = 0;\n"
         "  logic c = 0;\n"
         "  int hits = 0;\n"
         "  int last = 0;\n"
         "  localparam int N = 3, M = 4;\n"
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

const char* const kThreeBs =
    "    #10 a = 1;\n"
    "    #10 a = 0; b = 1;\n"
    "    #30 b = 0; c = 1;\n"
    "    #10 c = 0;\n";

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

TEST(SequenceRepetition, UnboundedConsecutiveRepetitionFillsTheMiddle) {
  SimFixture f;
  auto* hits = RunAndFindVar(RepetitionSource("a ##1 b[*1:$] ##1 c", kThreeBs),
                             f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
}

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

const char* const kTwoBsApart =
    "    #10 a = 1;\n"
    "    #10 a = 0; b = 1;\n"
    "    #10 b = 0;\n"
    "    #10 b = 1;\n"
    "    #10 b = 0; c = 1;\n"
    "    #10 c = 0;\n";

TEST(SequenceRepetition, GotoRepetitionEndsAtTheLastMatch) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      RepetitionSource("a ##1 b[->2:3] ##1 c", kTwoBsApart), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
}

TEST(SequenceRepetition, NonconsecutiveRepetitionExtendsPastTheLastMatch) {
  const char* const kTwoThenGap =
      "    #10 a = 1;\n"
      "    #10 a = 0; b = 1;\n"
      "    #20 b = 0;\n"
      "    #10 c = 1;\n"
      "    #10 c = 0;\n";
  SimFixture f;
  auto* hits = RunAndFindVar(
      RepetitionSource("a ##1 b[=2:3] ##1 c", kTwoThenGap), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
  SimFixture g;
  auto* goto_hits = RunAndFindVar(
      RepetitionSource("a ##1 b[->2:3] ##1 c", kTwoThenGap), g, "hits");
  ASSERT_NE(goto_hits, nullptr);
  EXPECT_EQ(goto_hits->value.ToUint64(), 0u);
}

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

TEST(SequenceRepetition, AParameterCountIsItsValue) {
  const char* const kDrive =
      "    a = 1;\n"
      "    #30 b = 1;\n"
      "    #10 b = 0;\n";
  SimFixture f;
  auto* hits =
      RunAndFindVar(RepetitionSource("a[*N] ##1 b", kDrive), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
  SimFixture g;
  auto* none =
      RunAndFindVar(RepetitionSource("a[*M] ##1 b", kDrive), g, "hits");
  ASSERT_NE(none, nullptr);
  EXPECT_EQ(none->value.ToUint64(), 0u);
}

TEST(SequenceRepetition, AFormalCountTakesItsActual) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0, a = 1, b = 0;\n"
      "  int hits = 0, last = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  sequence s(int k);\n"
      "    @(posedge clk) a[*k] ##1 b;\n"
      "  endsequence\n"
      "  initial begin #30 b = 1; #10 b = 0; #40 $finish; end\n"
      "  c1: cover property (s(3)) begin hits++; last = $time; end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
}

struct RepetitionRun {
  const char* body;
  const char* drive;
  uint64_t hits;
  uint64_t last;
};

void ExpectRepetitionRuns(std::initializer_list<RepetitionRun> runs) {
  for (const RepetitionRun& run : runs) {
    SCOPED_TRACE(run.body);
    SimFixture f;
    auto* hits =
        RunAndFindVar(RepetitionSource(run.body, run.drive), f, "hits");
    ASSERT_NE(hits, nullptr);
    EXPECT_EQ(hits->value.ToUint64(), run.hits);
    EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), run.last);
  }
}

const char* const kTwoGroupsThenC =
    "    #10 a = 1;\n"
    "    #10 a = 0; b = 1;\n"
    "    #10 b = 0; a = 1;\n"
    "    #10 a = 0; b = 1;\n"
    "    #10 b = 0; c = 1;\n"
    "    #10 c = 0;\n";

const char* const kOneGroupThenC =
    "    #10 a = 1;\n"
    "    #10 a = 0; b = 1;\n"
    "    #10 b = 0; c = 1;\n"
    "    #10 c = 0;\n";

TEST(SequenceRepetition, AGroupRepeatedByARangeMatchesEachCountInIt) {
  ExpectRepetitionRuns(
      {RepetitionRun{"(a ##1 b)[*1:2] ##1 c", kTwoGroupsThenC, 1, 55},
       RepetitionRun{"(a ##1 b)[*1:2] ##1 c", kOneGroupThenC, 1, 35},
       RepetitionRun{"(a ##1 b)[*2:3] ##1 c", kTwoGroupsThenC, 1, 55},
       RepetitionRun{"(a ##1 b)[*2:3] ##1 c", kOneGroupThenC, 0, 0}});
}

TEST(SequenceRepetition, AGroupRepeatedUnboundedlyMatchesEveryRun) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      RepetitionSource("(a ##1 b)[*1:$] ##1 c", kTwoGroupsThenC), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
}

TEST(SequenceRepetition, AGroupRepeatedFromZeroAdmitsTheEmptyMatch) {
  const char* const kBThenC =
      "    #10 b = 1;\n"
      "    #10 b = 0; c = 1;\n"
      "    #10 c = 0;\n";
  const char* const kBThenTwoAsThenC =
      "    #10 b = 1;\n"
      "    #10 b = 0; a = 1;\n"
      "    #20 a = 0; c = 1;\n"
      "    #10 c = 0;\n";
  ExpectRepetitionRuns(
      {RepetitionRun{"b ##1 (a ##1 a)[*0:1] ##1 c", kBThenC, 1, 25},
       RepetitionRun{"b ##1 (a ##1 a)[*0] ##1 c", kBThenC, 1, 25},
       RepetitionRun{"b ##1 (a ##1 a)[*0:1] ##1 c", kBThenTwoAsThenC, 1, 45},
       RepetitionRun{"b ##1 (a ##1 a)[*0] ##1 c", kBThenTwoAsThenC, 0, 0}});
}

TEST(SequenceRepetition, AnInstanceRepeatedByARangeMatchesOneRun) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0, a = 0, b = 0, c = 0;\n"
      "  int hits = 0, last = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  sequence ab; a ##1 b; endsequence\n"
      "  initial begin\n" +
          std::string(kOneGroupThenC) +
          "    #40 $finish;\n"
          "  end\n"
          "  c1: cover property (@(posedge clk) ab[*1:2] ##1 c) begin\n"
          "    hits++;\n"
          "    last = $time;\n"
          "  end\n"
          "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
}

TEST(SequenceRepetition, APropertyRepeatingAGroupByARangeIsEvaluated) {
  SimFixture f;
  auto* fails = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0, a = 0, b = 0, c = 0;\n"
      "  int fails = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  property p;\n"
      "    @(posedge clk) (a ##1 b)[*1:2] |=> c;\n"
      "  endproperty\n"
      "  a1: assert property (p) else fails++;\n"
      "  initial begin\n"
      "    #10 a = 1;\n"
      "    #10 a = 0; b = 1;\n"
      "    #10 b = 0;\n"
      "    #40 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "fails");
  ASSERT_NE(fails, nullptr);
  EXPECT_EQ(fails->value.ToUint64(), 1u);
}

}  // namespace
