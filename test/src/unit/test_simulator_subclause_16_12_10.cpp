#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_property_places.h"
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

TEST(SvaEngine, WeakNexttimeTakesInnerVerdictAtNextTick) {
  EXPECT_EQ(EvalNexttime(false, true, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalNexttime(false, true, PropertyResult::kFail),
            PropertyResult::kFail);
}

TEST(SvaEngine, WeakNexttimePassesWhenNoFurtherTick) {
  EXPECT_EQ(EvalNexttime(false, false, PropertyResult::kFail),
            PropertyResult::kPass);
}

TEST(SvaEngine, StrongNexttimeTakesInnerVerdictAtNextTick) {
  EXPECT_EQ(EvalNexttime(true, true, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalNexttime(true, true, PropertyResult::kFail),
            PropertyResult::kFail);
}

TEST(SvaEngine, StrongNexttimeFailsWhenNoFurtherTick) {
  EXPECT_EQ(EvalNexttime(true, false, PropertyResult::kPass),
            PropertyResult::kFail);
}

TEST(SvaEngine, NexttimeIndexCountsFromCurrentStep) {
  EXPECT_TRUE(NexttimeTargetReachable(2, 2));
  EXPECT_TRUE(NexttimeTargetReachable(2, 3));
  EXPECT_FALSE(NexttimeTargetReachable(2, 1));
}

TEST(SvaEngine, NexttimeZeroIndexIsAlignmentOperator) {
  EXPECT_TRUE(NexttimeTargetReachable(0, 0));
  EXPECT_TRUE(NexttimeTargetReachable(0, 5));
}

TEST(SvaEngine, NexttimeIndexOneMatchesNextTick) {
  EXPECT_TRUE(NexttimeTargetReachable(1, 1));
  EXPECT_TRUE(NexttimeTargetReachable(1, 4));
  EXPECT_FALSE(NexttimeTargetReachable(1, 0));
}

TEST(SvaEngine, IndexedNexttimeComposesReachabilityWithStrength) {
  bool reachable = NexttimeTargetReachable(3, 1);
  EXPECT_EQ(EvalNexttime(false, reachable, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalNexttime(true, reachable, PropertyResult::kPass),
            PropertyResult::kFail);

  reachable = NexttimeTargetReachable(3, 3);
  EXPECT_EQ(EvalNexttime(false, reachable, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalNexttime(true, reachable, PropertyResult::kFail),
            PropertyResult::kFail);
}

TEST(SvaEngine, ReachableNexttimePassesInnerVacuousVerdictThrough) {
  EXPECT_EQ(EvalNexttime(false, true, PropertyResult::kVacuousPass),
            PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalNexttime(true, true, PropertyResult::kVacuousPass),
            PropertyResult::kVacuousPass);
}

std::string NexttimeSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic a;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign a = tick inside {2, 3};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

TEST(NexttimeProperty, WeakNexttimeHoldsWithoutAFurtherTick) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      NexttimeSource("  p: assert property (@(posedge clk) nexttime a) "
                     "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(passes->value.ToUint64(), 3u);
}

TEST(NexttimeProperty, StrongNexttimeFailsWithoutAFurtherTick) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      NexttimeSource("  p: assert property (@(posedge clk) s_nexttime a) "
                     "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

TEST(NexttimeProperty, IndexedFormsCountTheTicks) {
  SimFixture f;
  auto* weak = RunAndFindVar(
      NexttimeSource("  p: assert property (@(posedge clk) nexttime [2] a) "
                     "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(weak, nullptr);
  EXPECT_EQ(weak->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(weak->value.ToUint64(), 3u);
  SimFixture g;
  auto* strong = RunAndFindVar(
      NexttimeSource("  p: assert property (@(posedge clk) s_nexttime [2] a) "
                     "passes++; else fails++;\n"),
      g, "passes");
  ASSERT_NE(strong, nullptr);
  EXPECT_EQ(strong->value.ToUint64(), 1u);
  g.ctx.RunFinalBlocks();
  EXPECT_EQ(g.ctx.FindVariable("fails")->value.ToUint64(), 3u);
}

TEST(NexttimeProperty, ZeroIndexIsTheCurrentTick) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      NexttimeSource("  p: assert property (@(posedge clk) nexttime [0] a) "
                     "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

constexpr const char* kPlacedStimulus =
    "  assign a = tick inside {1, 3};\n"
    "  assign b = tick inside {2, 3};\n"
    "  assign c = tick inside {2, 4};\n"
    "  assign d = tick inside {1, 2, 3};\n";

constexpr const char* kPlacedDeclarations =
    "  property q(x, y); x |-> y; endproperty\n";

const PlacedProperty kPlacedProperties[] = {
    {"nexttime c", {3, 1}, 3},
    {"s_nexttime c", {2, 2}, 2},
    {"nexttime [1] c", {3, 1}, 3},
    {"s_nexttime [1] c", {2, 2}, 2},
    {"nexttime [2] b", {3, 1}, 3},
    {"s_nexttime [2] b", {1, 3}, 1},
    {"nexttime [0] b", {2, 2}, 2},
    {"s_nexttime [0] b", {2, 2}, 2},
    {"nexttime always d", {1, 3}, 1},
    {"s_nexttime always d", {0, 4}, 0},
    {"nexttime s_eventually b", {3, 1}, 3},
    {"s_nexttime s_eventually b", {2, 2}, 2},
    {"a |-> s_nexttime [2] b", {3, 1}, 3},
    {"nexttime (b |-> c)", {3, 1}, 3},
    {"nexttime q(b, c)", {3, 1}, 3}};

TEST(NexttimeProperty, ANexttimeCountsInEachPlace) {
  for (const char* place : kPropertyPlaces) {
    for (const PlacedProperty& property : kPlacedProperties) {
      ExpectPropertyCountsInPlace(place, property, kPlacedStimulus,
                                  kPlacedDeclarations);
    }
  }
}

TEST(NexttimeProperty, DISABLED_ANexttimeCountsInACompilationUnitProperty) {
  for (const PlacedProperty& property : kPlacedProperties) {
    ExpectPropertyCountsInPlace("unit", property, kPlacedStimulus,
                                kPlacedDeclarations);
  }
}

TEST(NexttimeProperty, AnOffTickNexttimeFirstAlignsToItsClock) {
  EXPECT_EQ(SlowClockConsequentCounts("nexttime [0] b"), (PlaceCounts{3, 1}));
  EXPECT_EQ(SlowClockConsequentCounts("s_nexttime [0] b"), (PlaceCounts{3, 1}));
  EXPECT_EQ(SlowClockConsequentCounts("nexttime b"), (PlaceCounts{3, 1}));
  EXPECT_EQ(SlowClockConsequentCounts("s_nexttime b"), (PlaceCounts{2, 2}));
  EXPECT_EQ(SlowClockConsequentCounts("s_nexttime [1] b"), (PlaceCounts{2, 2}));
}

}  // namespace
