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

TEST(SvaEngine, SequenceOperatorIntersect) {
  EXPECT_TRUE(EvalSequenceIntersect(true, true, 3, 3));

  EXPECT_FALSE(EvalSequenceIntersect(true, true, 3, 4));
  EXPECT_FALSE(EvalSequenceIntersect(true, false, 3, 3));
}

TEST(SvaEngine, FirstMatchHasNoMatchWhenOperandDoesNotMatch) {
  auto fm = EvalFirstMatch({});
  EXPECT_FALSE(fm.matched);
  EXPECT_TRUE(fm.end_times.empty());
}

TEST(SvaEngine, FirstMatchKeepsOnlyEarliestEndingMatch) {
  auto fm = EvalFirstMatch({5, 3, 4, 2});
  EXPECT_TRUE(fm.matched);
  EXPECT_EQ(fm.end_times, std::vector<uint32_t>{2});
}

TEST(SvaEngine, FirstMatchKeepsAllMatchesSharingEarliestEndTick) {
  auto fm = EvalFirstMatch({4, 4, 6});
  EXPECT_TRUE(fm.matched);
  std::vector<uint32_t> expected{4, 4};
  EXPECT_EQ(fm.end_times, expected);
}

TEST(SvaEngine, FirstMatchKeepsSingleOperandMatch) {
  auto fm = EvalFirstMatch({7});
  EXPECT_TRUE(fm.matched);
  EXPECT_EQ(fm.end_times, std::vector<uint32_t>{7});
}

TEST(SvaEngine, FirstMatchRetainsAllWhenEveryMatchTiesOnSameTick) {
  auto fm = EvalFirstMatch({3, 3, 3});
  EXPECT_TRUE(fm.matched);
  std::vector<uint32_t> expected{3, 3, 3};
  EXPECT_EQ(fm.end_times, expected);
}

TEST(SequenceFirstMatch, KeepsTheEarliestEndingMatchOfAnAttempt) {
  const std::string kDrive = DriveTicks({{1}, {3, 4, 5, 6}, {}, {}, {}});
  SimFixture f;
  auto* all =
      RunAndFindVar(SequenceTickSource("te1 ##[2:5] te2", kDrive), f, "hits");
  ASSERT_NE(all, nullptr);
  EXPECT_EQ(all->value.ToUint64(), 4u);
  SimFixture g;
  auto* first = RunAndFindVar(
      SequenceTickSource("first_match(te1 ##[2:5] te2)", kDrive), g, "hits");
  ASSERT_NE(first, nullptr);
  EXPECT_EQ(first->value.ToUint64(), 1u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 25u);
}

TEST(SequenceFirstMatch, HasNoMatchWhereTheOperandHasNone) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceTickSource("first_match(te1 ##[2:5] te2)",
                                       DriveTicks({{1}, {2, 7}, {}, {}, {}})),
                    f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 0u);
}

TEST(SequenceFirstMatch, TakesTheEarliestEndOverTheOrOperands) {
  const std::string kBody =
      "first_match((te1 ##[2:3] te2) or (te3 ##[1:2] te4))";
  SimFixture f;
  auto* second_first = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{1}, {3, 4}, {1}, {2}, {}})), f,
      "hits");
  ASSERT_NE(second_first, nullptr);
  EXPECT_EQ(second_first->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 15u);
  SimFixture g;
  auto* tied = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{1}, {3, 4}, {1}, {3}, {}})), g,
      "hits");
  ASSERT_NE(tied, nullptr);
  EXPECT_EQ(tied->value.ToUint64(), 1u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 25u);
}

TEST(SequenceFirstMatch, EachAttemptKeepsItsOwnEarliestMatch) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource("first_match(te1 ##[2:5] te2)",
                         DriveTicks({{1, 2}, {3, 4, 5, 6}, {}, {}, {}})),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
}

std::string FirstMatchAntecedentSource(const std::string& antecedent) {
  return "module t;\n"
         "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
         "  bit [0:9] av = 10'b1000100000, bv = 10'b0110011000,\n"
         "            cv = 10'b0100010000;\n"
         "  bit a, b, c;\n"
         "  assign a = av[0]; assign b = bv[0]; assign c = cv[0];\n"
         "  always @(negedge clk) begin\n"
         "    av <= av << 1; bv <= bv << 1; cv <= cv << 1;\n"
         "  end\n"
         "  int p = 0, f = 0;\n"
         "  sequence s; first_match(a ##[1:3] b); endsequence\n"
         "  assert property (@(posedge clk) " +
         antecedent +
         " |-> c) p++; else f++;\n"
         "endmodule\n";
}

TEST(FirstMatchAntecedent, TheConsequentIsCheckedAtTheEarliestEndOnly) {
  SimFixture f;
  auto* p = RunAndFindVar(
      FirstMatchAntecedentSource("first_match(a ##[1:3] b)"), f, "p");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("f")->value.ToUint64(), 0u);
}

TEST(FirstMatchAntecedent, ANamedFirstMatchSequenceEndsAtItsFirstMatch) {
  SimFixture f;
  auto* p = RunAndFindVar(FirstMatchAntecedentSource("s"), f, "p");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("f")->value.ToUint64(), 0u);
}

TEST(FirstMatchAntecedent, EveryEndOfAPlainAntecedentBeginsAConsequent) {
  SimFixture f;
  auto* p = RunAndFindVar(FirstMatchAntecedentSource("(a ##[1:3] b)"), f, "p");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->value.ToUint64(), 8u);
  EXPECT_EQ(f.ctx.FindVariable("f")->value.ToUint64(), 2u);
}

}  // namespace
