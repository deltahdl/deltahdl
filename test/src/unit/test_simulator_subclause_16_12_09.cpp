#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine_properties.h"
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

TEST(SvaEngine, OverlappingFollowedBy) {
  EXPECT_EQ(EvalFollowedBy(true, true, false), PropertyResult::kPass);
  EXPECT_EQ(EvalFollowedBy(true, false, false), PropertyResult::kFail);
}

TEST(SvaEngine, FollowedByRequiresAntecedentMatch) {
  EXPECT_EQ(EvalFollowedBy(false, true, false), PropertyResult::kFail);
  EXPECT_EQ(EvalFollowedBy(false, false, false), PropertyResult::kFail);
  EXPECT_EQ(EvalFollowedBy(false, true, true), PropertyResult::kFail);
  EXPECT_EQ(EvalFollowedBy(false, false, true), PropertyResult::kFail);
}

TEST(SvaEngine, NonOverlappingFollowedByDefers) {
  EXPECT_EQ(EvalFollowedBy(true, true, true), PropertyResult::kPending);
  EXPECT_EQ(EvalFollowedBy(true, false, true), PropertyResult::kPending);
}

TEST(SvaEngine, NonOverlappingFollowedByEmptyMatchSettlesImmediately) {
  EXPECT_EQ(EvalFollowedBy(true, true, true, true), PropertyResult::kPass);
  EXPECT_EQ(EvalFollowedBy(true, false, true, true), PropertyResult::kFail);
  EXPECT_EQ(EvalFollowedBy(true, true, true, false), PropertyResult::kPending);
}

TEST(SvaEngine, NonOverlappingFollowedByResolvesPass) {
  EXPECT_EQ(EvalFollowedBy(true, false, true), PropertyResult::kPending);
  EXPECT_EQ(ResolveFollowedByNonOverlapping(true), PropertyResult::kPass);
}

TEST(SvaEngine, NonOverlappingFollowedByResolvesFail) {
  EXPECT_EQ(EvalFollowedBy(true, false, true), PropertyResult::kPending);
  EXPECT_EQ(ResolveFollowedByNonOverlapping(false), PropertyResult::kFail);
}

TEST(SvaEngine, OverlappingFollowedByMatchesImplicationDual) {
  for (bool a : {false, true}) {
    for (bool c : {false, true}) {
      PropertyResult dual = EvalPropertyNot(EvalImplication(a, !c, false));
      EXPECT_EQ(EvalFollowedBy(a, c, false), dual);
    }
  }
}

TEST(SvaEngine, NonOverlappingFollowedByMatchesImplicationDual) {
  for (bool a : {false, true}) {
    for (bool c : {false, true}) {
      PropertyResult implied = EvalImplication(a, !c, true);
      PropertyResult dual = (implied == PropertyResult::kPending)
                                ? PropertyResult::kPending
                                : EvalPropertyNot(implied);
      EXPECT_EQ(EvalFollowedBy(a, c, true), dual);
    }
  }
}

std::string FollowedBySource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic req, gnt, done, rst;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign req = tick inside {1, 2, 4};\n"
         "  assign gnt = tick inside {1, 4};\n"
         "  assign done = tick inside {3};\n"
         "  assign rst = tick inside {2};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

TEST(FollowedByProperty, OverlappedNeedsAMatchWithTheConsequentTrue) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      FollowedBySource("  p: assert property (@(posedge clk) req #-# gnt) "
                       "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

TEST(FollowedByProperty, NonoverlappedReadsTheConsequentTheTickAfter) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      FollowedBySource("  p: assert property (@(posedge clk) req #=# gnt) "
                       "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 3u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 4u);
}

TEST(FollowedByProperty, WindowedAntecedentIsTrueAtTheMatchWithTheConsequent) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      FollowedBySource("  p: assert property (@(posedge clk) ##[0:5] done #-# "
                       "!rst) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 0u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

TEST(FollowedByProperty, IsTheDualOfTheImplication) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      FollowedBySource("  p: assert property (@(posedge clk) not (req |-> not "
                       "gnt)) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

}  // namespace
