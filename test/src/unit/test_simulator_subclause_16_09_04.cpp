#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "builders_systask.h"
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
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

TEST(SvaEngine, GotoRepetition) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kGotoRepetition;
  seq.rep_min = 2;
  seq.rep_max = 2;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchGotoRepetition(seq, {0, 1, 0, 1}));

  EXPECT_FALSE(MatchGotoRepetition(seq, {0, 1, 0, 0}));
}

TEST(SvaEngine, GotoRepetitionEndsAtMatch) {
  SvaSequence seq;
  seq.kind = SvaSequenceKind::kGotoRepetition;
  seq.rep_min = 1;
  seq.rep_max = 1;
  seq.expr_check = [](uint64_t v) { return v == 1; };

  EXPECT_TRUE(MatchGotoRepetition(seq, {0, 0, 1}));
  EXPECT_FALSE(MatchGotoRepetition(seq, {0, 1, 0}));
}

TEST(GlobalClockingSampledValue, PastEdgeFunctions) {
  EXPECT_TRUE(RoseGclk(0, 1));
  EXPECT_FALSE(RoseGclk(1, 1));
  EXPECT_TRUE(FellGclk(1, 0));
  EXPECT_FALSE(FellGclk(0, 0));
}

TEST(GlobalClockingSampledValue, PastStableAndChanged) {
  EXPECT_TRUE(StableGclk(5, 5));
  EXPECT_FALSE(StableGclk(5, 6));
  EXPECT_TRUE(ChangedGclk(5, 6));
  EXPECT_FALSE(ChangedGclk(5, 5));
}

TEST(GlobalClockingSampledValue, FutureEdgeFunctions) {
  EXPECT_TRUE(RisingGclk(0, 1));
  EXPECT_FALSE(RisingGclk(1, 1));
  EXPECT_TRUE(FallingGclk(1, 0));
  EXPECT_FALSE(FallingGclk(0, 0));
}

TEST(GlobalClockingSampledValue, ChangingIsComplementOfSteady) {
  EXPECT_TRUE(SteadyGclk(3, 3));
  EXPECT_FALSE(SteadyGclk(3, 4));
  EXPECT_EQ(ChangingGclk(3, 3), !SteadyGclk(3, 3));
  EXPECT_EQ(ChangingGclk(3, 4), !SteadyGclk(3, 4));
}

TEST(GlobalClockingSampledValue, FutureActionBlockDelayedToFollowingTick) {
  EXPECT_TRUE(GclkFutureActionBlockDelayedToFollowingGlobalTick());
}

TEST(GlobalClockingSampledValue, FutureKillTimingBoundsTheAttempt) {
  EXPECT_TRUE(GclkFutureKillAffectsAttempt(true));
  EXPECT_FALSE(GclkFutureKillAffectsAttempt(false));
}

TEST(GlobalClockingSampledValue, FutureDisableIffBoundedByAttemptInterval) {
  EXPECT_FALSE(GclkFutureAttemptDisabledByDisableIff(82, 80));
  EXPECT_TRUE(GclkFutureAttemptDisabledByDisableIff(80, 80));
}

TEST(GlobalClockingSampledValue, EvalValueBearingFunctions) {
  SysTaskFixture f;
  auto* past = MkSysCall(f.arena, "$past_gclk", {MkInt(f.arena, 42)});
  EXPECT_EQ(EvalExpr(past, f.ctx, f.arena).ToUint64(), 42u);
  auto* future = MkSysCall(f.arena, "$future_gclk", {MkInt(f.arena, 7)});
  EXPECT_EQ(EvalExpr(future, f.ctx, f.arena).ToUint64(), 7u);
}

TEST(GlobalClockingSampledValue, EvalValueChangeFunctionsAreOneBit) {
  SysTaskFixture f;
  auto* rose = MkSysCall(f.arena, "$rose_gclk", {MkInt(f.arena, 1)});
  EXPECT_EQ(EvalExpr(rose, f.ctx, f.arena).width, 1u);
  auto* changing = MkSysCall(f.arena, "$changing_gclk", {MkInt(f.arena, 1)});
  EXPECT_EQ(EvalExpr(changing, f.ctx, f.arena).width, 1u);
}

TEST(GlobalClockingSampledValue, EdgeFunctionsUseLeastSignificantBit) {
  EXPECT_TRUE(RoseGclk(0b10, 0b11));
  EXPECT_FALSE(RoseGclk(0b11, 0b10));
  EXPECT_TRUE(FellGclk(0b01, 0b10));
  EXPECT_TRUE(RisingGclk(0b100, 0b101));
  EXPECT_TRUE(FallingGclk(0b011, 0b010));
}

TEST(GlobalClockingSampledValue, StableComparesWholeValue) {
  EXPECT_FALSE(StableGclk(0b10, 0b00));
  EXPECT_TRUE(ChangedGclk(0b10, 0b00));
}

TEST(GlobalClockingSampledValue, EvalWithMissingArgumentIsDefined) {
  SysTaskFixture f;
  auto* past = MkSysCall(f.arena, "$past_gclk", {});
  EXPECT_EQ(EvalExpr(past, f.ctx, f.arena).ToUint64(), 0u);
}

TEST(GlobalClockingFutureSim,
     RisingGclkHoldsWhereTheOperandRisesByTheNextTick) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic aclk = 1'b0;\n"
      "  logic gclk = 1'b0;\n"
      "  logic req = 1'b0;\n"
      "  int hits = 0;\n"
      "  global clocking gc @(posedge gclk); endclocking\n"
      "  assert property (@(posedge aclk) $rising_gclk(req)) hits = hits + 1;\n"
      "  initial begin\n"
      "    #5 aclk = 1'b1;\n"
      "    #2 req = 1'b1;\n"
      "    #3 gclk = 1'b1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
}

TEST(GlobalClockingFutureSim, RisingGclkFailsWhereTheOperandIsSteady) {
  SimFixture f;
  auto* misses = RunAndFindVar(
      "module t;\n"
      "  logic aclk = 1'b0;\n"
      "  logic gclk = 1'b0;\n"
      "  logic req = 1'b0;\n"
      "  int hits = 0;\n"
      "  int misses = 0;\n"
      "  global clocking gc @(posedge gclk); endclocking\n"
      "  assert property (@(posedge aclk) $rising_gclk(req)) hits = hits + 1;\n"
      "  else misses = misses + 1;\n"
      "  initial begin\n"
      "    #5 aclk = 1'b1;\n"
      "    #5 gclk = 1'b1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "misses");
  ASSERT_NE(misses, nullptr);
  EXPECT_EQ(misses->value.ToUint64(), 1u);
}

TEST(GlobalClockingFutureSim, SteadyGclkHoldsOverAnOperandThatDoesNotChange) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic aclk = 1'b0;\n"
      "  logic gclk = 1'b0;\n"
      "  logic [3:0] v = 4'd5;\n"
      "  int hits = 0;\n"
      "  global clocking gc @(posedge gclk); endclocking\n"
      "  assert property (@(posedge aclk) $steady_gclk(v)) hits = hits + 1;\n"
      "  initial begin\n"
      "    #5 aclk = 1'b1;\n"
      "    #5 gclk = 1'b1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
}

TEST(GlobalClockingFutureSim, FutureGclkReadsTheValueAtTheNextGlobalTick) {
  SimFixture f;
  auto* agree = RunAndFindVar(
      "module t;\n"
      "  logic aclk = 1'b0;\n"
      "  logic gclk = 1'b0;\n"
      "  logic [7:0] v = 8'd0;\n"
      "  int agree = 0;\n"
      "  global clocking gc @(posedge gclk); endclocking\n"
      "  assert property (@(posedge aclk) $future_gclk(v) == 8'd7)\n"
      "    agree = agree + 1;\n"
      "  initial begin\n"
      "    #5 aclk = 1'b1;\n"
      "    #2 v = 8'd7;\n"
      "    #3 gclk = 1'b1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "agree");
  ASSERT_NE(agree, nullptr);
  EXPECT_EQ(agree->value.ToUint64(), 1u);
}

TEST(GlobalClockingFutureSim, TheActionBlockRunsAtTheFollowingGlobalTick) {
  SimFixture f;
  auto* when = RunAndFindVar(
      "module t;\n"
      "  logic aclk = 1'b0;\n"
      "  logic gclk = 1'b0;\n"
      "  logic [3:0] v = 4'd5;\n"
      "  int when = 0;\n"
      "  global clocking gc @(posedge gclk); endclocking\n"
      "  assert property (@(posedge aclk) $steady_gclk(v)) when = $time;\n"
      "  initial begin\n"
      "    #5 aclk = 1'b1;\n"
      "    #5 gclk = 1'b1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "when");
  ASSERT_NE(when, nullptr);
  EXPECT_EQ(when->value.ToUint64(), 10u);
}

TEST(GlobalClockingFutureSim, AnAttemptStartsAtEveryTickWhileOneIsWaiting) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic gclk = 1'b0;\n"
      "  logic v = 1'b0;\n"
      "  int hits = 0;\n"
      "  int last = 0;\n"
      "  global clocking gc @(posedge gclk); endclocking\n"
      "  assert property (@(posedge gclk) $rising_gclk(v)) begin\n"
      "    hits = hits + 1; last = $time;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 gclk = 1'b1; v = 1'b1; #5 gclk = 1'b0;\n"
      "    #5 gclk = 1'b1; #5 gclk = 1'b0;\n"
      "    #5 gclk = 1'b1; v = 1'b0; #5 gclk = 1'b0;\n"
      "    #5 gclk = 1'b1; v = 1'b1; #5 gclk = 1'b0;\n"
      "    #5 gclk = 1'b1; #5 gclk = 1'b0;\n"
      "    #5 gclk = 1'b1; v = 1'b0; #5 gclk = 1'b0;\n"
      "    #5 gclk = 1'b1; #5 gclk = 1'b0;\n"
      "    #5 gclk = 1'b1; #5 gclk = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  auto* last = f.ctx.FindVariable("last");
  ASSERT_NE(last, nullptr);
  EXPECT_EQ(last->value.ToUint64(), 45u);
}

TEST(GlobalClockingFutureSim, AnImplicationFailsAtTheGlobalTickAfterItsLast) {
  SimFixture f;
  auto* when = RunAndFindVar(
      "module t;\n"
      "  logic aclk = 1'b0, gclk = 1'b0, a = 1'b1, b = 1'b0;\n"
      "  int when = 0;\n"
      "  global clocking gc @(posedge gclk); endclocking\n"
      "  assert property (@(posedge aclk) $falling_gclk(a) |=> b)\n"
      "    else when = $time;\n"
      "  initial begin\n"
      "    #5 aclk = 1'b1;\n"
      "    #2 a = 1'b0;\n"
      "    #3 gclk = 1'b1; aclk = 1'b0;\n"
      "    #5 gclk = 1'b0; aclk = 1'b1;\n"
      "    #5 gclk = 1'b1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "when");
  ASSERT_NE(when, nullptr);
  EXPECT_EQ(when->value.ToUint64(), 20u);
}

TEST(GlobalClockingFutureSim, ASequencesVerdictsComeAtTheGlobalTickAfterThem) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      "module t;\n"
      "  logic aclk = 1'b0, gclk = 1'b0, a = 1'b0, b = 1'b1;\n"
      "  int passes = 0, fails = 0, when = 0;\n"
      "  global clocking gc @(posedge gclk); endclocking\n"
      "  assert property (@(posedge aclk) $rising_gclk(a) ##1 b)\n"
      "    passes = passes + 1;\n"
      "    else begin fails = fails + 1; when = $time; end\n"
      "  initial begin\n"
      "    #5 aclk = 1'b1;\n"
      "    #2 a = 1'b1;\n"
      "    #3 gclk = 1'b1; aclk = 1'b0;\n"
      "    #5 gclk = 1'b0; aclk = 1'b1;\n"
      "    #5 gclk = 1'b1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  auto* fails = f.ctx.FindVariable("fails");
  ASSERT_NE(fails, nullptr);
  EXPECT_EQ(fails->value.ToUint64(), 1u);
  auto* when = f.ctx.FindVariable("when");
  ASSERT_NE(when, nullptr);
  EXPECT_EQ(when->value.ToUint64(), 20u);
}

TEST(GlobalClockingFutureSim, AnOperandBesideAFutureFunctionIsReadAtItsTick) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic aclk = 1'b0, gclk = 1'b0, req = 1'b0, en = 1'b1;\n"
      "  int hits = 0;\n"
      "  global clocking gc @(posedge gclk); endclocking\n"
      "  assert property (@(posedge aclk) $rising_gclk(req) && en)\n"
      "    hits = hits + 1;\n"
      "  initial begin\n"
      "    #5 aclk = 1'b1;\n"
      "    #2 req = 1'b1; en = 1'b0;\n"
      "    #3 gclk = 1'b1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
}

TEST(GlobalClockingFutureSim, AMulticlockedImplicationFailsAtTheGlobalTick) {
  SimFixture f;
  auto* when = RunAndFindVar(
      "module t;\n"
      "  logic clk = 1'b0, clk2 = 1'b0, gclk = 1'b0, a = 1'b0, b = 1'b0;\n"
      "  int when = 0;\n"
      "  global clocking gc @(posedge gclk); endclocking\n"
      "  assert property (@(posedge clk) $rising_gclk(a) |=>\n"
      "                   @(posedge clk2) b)\n"
      "    else when = $time;\n"
      "  initial begin\n"
      "    #5 clk = 1'b1;\n"
      "    #2 a = 1'b1;\n"
      "    #3 gclk = 1'b1;\n"
      "    #5 gclk = 1'b0; clk2 = 1'b1;\n"
      "    #5 gclk = 1'b1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "when");
  ASSERT_NE(when, nullptr);
  EXPECT_EQ(when->value.ToUint64(), 20u);
}

}  // namespace
