#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

TEST(SvaEngine, EmptyConcatZeroDelayLeftNoMatch) {
  EmptyConcatResult r = ConcatEmptyMatch(EmptyConcatSide::kEmptyLeft, 0);
  EXPECT_FALSE(r.matchable);
}

TEST(SvaEngine, EmptyConcatZeroDelayRightNoMatch) {
  EmptyConcatResult r = ConcatEmptyMatch(EmptyConcatSide::kEmptyRight, 0);
  EXPECT_FALSE(r.matchable);
}

TEST(SvaEngine, EmptyConcatLeftCollapsesDelay) {
  EmptyConcatResult r = ConcatEmptyMatch(EmptyConcatSide::kEmptyLeft, 2);
  EXPECT_TRUE(r.matchable);
  EXPECT_EQ(r.effective_delay, 1u);
  EXPECT_FALSE(r.append_true);
}

TEST(SvaEngine, EmptyConcatRightCollapsesDelayWithTrue) {
  EmptyConcatResult r = ConcatEmptyMatch(EmptyConcatSide::kEmptyRight, 2);
  EXPECT_TRUE(r.matchable);
  EXPECT_EQ(r.effective_delay, 1u);
  EXPECT_TRUE(r.append_true);
}

TEST(SvaEngine, EmptyAtZeroDelayNeverMatchesButFusionDoes) {
  EXPECT_FALSE(ConcatEmptyMatch(EmptyConcatSide::kEmptyRight, 0).matchable);

  SvaSequence b;
  b.kind = SvaSequenceKind::kDelay;
  b.delay_cycles = 0;
  b.expr_check = [](uint64_t v) { return v == 1; };
  EXPECT_TRUE(MatchDelaySequence(b, {1}));
  EXPECT_FALSE(MatchDelaySequence(b, {0}));
}

TEST(SvaEngine, RangeAdmittingEmptyIsOrOfCases) {
  EXPECT_TRUE(MatchEmptyOrNonempty(0, true, false));
  EXPECT_TRUE(MatchEmptyOrNonempty(0, false, true));
  EXPECT_FALSE(MatchEmptyOrNonempty(0, false, false));

  EXPECT_FALSE(MatchEmptyOrNonempty(1, true, false));
  EXPECT_TRUE(MatchEmptyOrNonempty(1, false, true));
}

TEST(SvaEngine, EmptyConcatRightMinimalDelayStillAppendsTrue) {
  EmptyConcatResult r = ConcatEmptyMatch(EmptyConcatSide::kEmptyRight, 1);
  EXPECT_TRUE(r.matchable);
  EXPECT_EQ(r.effective_delay, 0u);
  EXPECT_TRUE(r.append_true);
}

TEST(SvaEngine, RangeAdmittingEmptyBothCasesMatch) {
  EXPECT_TRUE(MatchEmptyOrNonempty(0, true, true));
}

TEST(SvaEngine, EmptyConcatLeftMinimalDelayDoesNotAppendTrue) {
  EmptyConcatResult r = ConcatEmptyMatch(EmptyConcatSide::kEmptyLeft, 1);
  EXPECT_TRUE(r.matchable);
  EXPECT_EQ(r.effective_delay, 0u);
  EXPECT_FALSE(r.append_true);
}

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

const char* const kBThenAb =
    "    #10 b = 1;\n"
    "    #10 a = 1;\n"
    "    #10 a = 0; b = 0;\n";

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
