#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_property_places.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SvaEngine, WeakAlwaysTakesInnerVerdictOverPresentTicks) {
  EXPECT_EQ(EvalAlways(false, true, true), PropertyResult::kPass);
  EXPECT_EQ(EvalAlways(false, true, false), PropertyResult::kFail);
}

TEST(SvaEngine, WeakAlwaysIgnoresMissingCoveredTicks) {
  EXPECT_EQ(EvalAlways(false, false, true), PropertyResult::kPass);
}

TEST(SvaEngine, StrongAlwaysRequiresPresentTicksAndInnerVerdict) {
  EXPECT_EQ(EvalAlways(true, true, true), PropertyResult::kPass);
  EXPECT_EQ(EvalAlways(true, true, false), PropertyResult::kFail);
}

TEST(SvaEngine, StrongAlwaysFailsWhenCoveredTickMissing) {
  EXPECT_EQ(EvalAlways(true, false, true), PropertyResult::kFail);
}

TEST(SvaEngine, NonRangedAlwaysCoversEveryFutureTick) {
  EXPECT_TRUE(AlwaysRangeCovers(0, 0, kAlwaysUnboundedMax));
  EXPECT_TRUE(AlwaysRangeCovers(9, 0, kAlwaysUnboundedMax));
}

TEST(SvaEngine, BoundedRangeCoversInclusiveSpan) {
  EXPECT_FALSE(AlwaysRangeCovers(1, 2, 4));
  EXPECT_TRUE(AlwaysRangeCovers(2, 2, 4));
  EXPECT_TRUE(AlwaysRangeCovers(4, 2, 4));
  EXPECT_FALSE(AlwaysRangeCovers(5, 2, 4));
}

TEST(SvaEngine, UnboundedRangeCoversFromMinimumOnward) {
  EXPECT_FALSE(AlwaysRangeCovers(2, 3, kAlwaysUnboundedMax));
  EXPECT_TRUE(AlwaysRangeCovers(3, 3, kAlwaysUnboundedMax));
  EXPECT_TRUE(AlwaysRangeCovers(100, 3, kAlwaysUnboundedMax));
}

TEST(SvaEngine, StrongAlwaysTicksPresentWhenEnoughFutureTicks) {
  EXPECT_TRUE(AlwaysStrongTicksAllPresent(3, 3));
  EXPECT_TRUE(AlwaysStrongTicksAllPresent(3, 5));
  EXPECT_FALSE(AlwaysStrongTicksAllPresent(3, 2));
}

TEST(SvaEngine, StrongAlwaysComposesPresenceWithInnerVerdict) {
  bool present = AlwaysStrongTicksAllPresent(4, 2);
  EXPECT_EQ(EvalAlways(true, present, true), PropertyResult::kFail);

  present = AlwaysStrongTicksAllPresent(4, 4);
  EXPECT_EQ(EvalAlways(true, present, true), PropertyResult::kPass);
}

std::string AlwaysSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic a, b;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign a = tick inside {1, 2, 3};\n"
         "  assign b = tick inside {1, 2, 3, 4};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

TEST(AlwaysProperty, WeakAlwaysHoldsUntilATickFails) {
  SimFixture f;
  auto* fails_at_four = RunAndFindVar(
      AlwaysSource("  p: assert property (@(posedge clk) always a) passes++; "
                   "else fails++;\n"),
      f, "passes");
  ASSERT_NE(fails_at_four, nullptr);
  EXPECT_EQ(fails_at_four->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 4u);
  SimFixture g;
  auto* holds = RunAndFindVar(
      AlwaysSource("  p: assert property (@(posedge clk) always b) passes++; "
                   "else fails++;\n"),
      g, "passes");
  ASSERT_NE(holds, nullptr);
  EXPECT_EQ(holds->value.ToUint64(), 0u);
  g.ctx.RunFinalBlocks();
  EXPECT_EQ(holds->value.ToUint64(), 4u);
  EXPECT_EQ(g.ctx.FindVariable("fails")->value.ToUint64(), 0u);
}

TEST(AlwaysProperty, RangedWeakAlwaysNeedsOnlyTheTicksThatExist) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      AlwaysSource("  p: assert property (@(posedge clk) always [0:1] b) "
                   "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 0u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(passes->value.ToUint64(), 4u);
}

TEST(AlwaysProperty, RangedStrongAlwaysNeedsEveryTickOfTheRange) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      AlwaysSource("  p: assert property (@(posedge clk) s_always [0:1] b) "
                   "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

TEST(AlwaysProperty, RangeBeginsAfterItsMinimum) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      AlwaysSource("  p: assert property (@(posedge clk) always [1:2] a) "
                   "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(passes->value.ToUint64(), 2u);
}

constexpr const char* kPlacedStimulus =
    "  assign a = tick inside {1, 3};\n"
    "  assign b = tick inside {2, 3};\n"
    "  assign c = tick inside {2, 4};\n"
    "  assign d = tick inside {1, 2, 3};\n";

constexpr const char* kPlacedDeclarations =
    "  property q(x, y); x |-> y; endproperty\n";

const PlacedProperty kPlacedProperties[] = {
    {"always d", {0, 4}, 0},
    {"always (c or d)", {4, 0}, 4},
    {"always c", {1, 3}, 1},
    {"always [0:1] d", {2, 2}, 2},
    {"always [0:1] (c or d)", {4, 0}, 4},
    {"s_always [0:1] (c or d)", {3, 1}, 3},
    {"s_always [0:2] (c or d)", {2, 2}, 2},
    {"always [1:2] b", {2, 2}, 2},
    {"s_always [1:2] b", {1, 3}, 1},
    {"always [0:0] b", {2, 2}, 2},
    {"s_always [0:0] b", {2, 2}, 2},
    {"always [2:2] a", {3, 1}, 3},
    {"s_always [2:2] a", {1, 3}, 1},
    {"always [2:$] c", {3, 1}, 3},
    {"always [1:$] d", {1, 3}, 1},
    {"a |-> always c", {2, 2}, 2},
    {"a ##1 b |=> always c", {3, 1}, 3},
    {"d[*3] #=# always !d", {1, 3}, 1},
    {"always q(b, c)", {1, 3}, 1}};

TEST(AlwaysProperty, AnAlwaysCountsInEachPlace) {
  for (const char* place : kPropertyPlaces) {
    for (const PlacedProperty& property : kPlacedProperties) {
      ExpectPropertyCountsInPlace(place, property, kPlacedStimulus,
                                  kPlacedDeclarations);
    }
  }
}

TEST(AlwaysProperty, DISABLED_AnAlwaysCountsInACompilationUnitProperty) {
  for (const PlacedProperty& property : kPlacedProperties) {
    ExpectPropertyCountsInPlace("unit", property, kPlacedStimulus,
                                kPlacedDeclarations);
  }
}

TEST(AlwaysProperty, AnOffTickAlwaysFirstAlignsToItsClock) {
  EXPECT_EQ(SlowClockConsequentCounts("always [0:0] b"), (PlaceCounts{3, 1}));
  EXPECT_EQ(SlowClockConsequentCounts("s_always [0:0] b"), (PlaceCounts{3, 1}));
  EXPECT_EQ(SlowClockConsequentCounts("always [1:1] b"), (PlaceCounts{3, 1}));
  EXPECT_EQ(SlowClockConsequentCounts("s_always [1:1] b"), (PlaceCounts{2, 2}));
  EXPECT_EQ(SlowClockConsequentCounts("s_always [0:1] b"), (PlaceCounts{2, 2}));
  EXPECT_EQ(SlowClockConsequentCounts("always b"), (PlaceCounts{2, 2}));
}

std::string FailureTimes(const std::string& statement) {
  SimFixture f;
  return RunCapture(
      PlacedTop(kPlacedStimulus,
                "  " + statement + " else $display(\"FAIL at %0t\", $time);\n"),
      f);
}

TEST(AlwaysProperty, AnExplicitAlwaysFailsWhereTheImplicitOneDoes) {
  EXPECT_EQ(FailureTimes("assert property (@(posedge clk) b |-> c)"),
            "FAIL at 25\n$finish at time 40\n");
  EXPECT_EQ(
      FailureTimes("initial assert property (@(posedge clk) always (b |-> c))"),
      "FAIL at 25\n$finish at time 40\n");
  EXPECT_EQ(CountThroughTheEnd(PlacedTop(
                kPlacedStimulus,
                "  initial assert property (@(posedge clk) always (c or d)) "
                "$display(\"PASS\"); else $display(\"FAIL\");\n")),
            (PlaceCounts{1, 0}));
}

}  // namespace
