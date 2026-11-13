#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_property_places.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SvaEngineEventually, StrongHoldsWithWitness) {
  EXPECT_EQ(EvalEventually(true, true, true), PropertyResult::kPass);
}

TEST(SvaEngineEventually, StrongFailsWithoutWitness) {
  EXPECT_EQ(EvalEventually(true, false, true), PropertyResult::kFail);
  EXPECT_EQ(EvalEventually(true, false, false), PropertyResult::kFail);
}

TEST(SvaEngineEventually, WeakHoldsWithWitness) {
  EXPECT_EQ(EvalEventually(false, true, true), PropertyResult::kPass);
}

TEST(SvaEngineEventually, WeakFailsWhenRangeFullyObservedWithoutWitness) {
  EXPECT_EQ(EvalEventually(false, false, true), PropertyResult::kFail);
}

TEST(SvaEngineEventually, WeakHoldsWhenRangeTicksMissing) {
  EXPECT_EQ(EvalEventually(false, false, false), PropertyResult::kPass);
}

TEST(SvaEngineEventually, WeakHoldsWithWitnessWhenRangeTicksMissing) {
  EXPECT_EQ(EvalEventually(false, true, false), PropertyResult::kPass);
}

TEST(SvaEngineEventually, NonRangedStrongTakesWitness) {
  EXPECT_EQ(EvalEventually(true, true, false), PropertyResult::kPass);
}

std::string EventuallySource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic a;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign a = tick inside {3};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

TEST(EventuallyProperty, StrongEventuallyNeedsAWitness) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      EventuallySource("  p: assert property (@(posedge clk) s_eventually a) "
                       "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 0u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

TEST(EventuallyProperty, RangedWeakEventuallyHoldsWhereTheRangeIsCutShort) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      EventuallySource("  p: assert property (@(posedge clk) eventually [0:1] "
                       "a) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(passes->value.ToUint64(), 3u);
}

TEST(EventuallyProperty, RangedStrongEventuallyFailsWhereTheRangeIsCutShort) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      EventuallySource("  p: assert property (@(posedge clk) s_eventually "
                       "[0:1] a) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

TEST(EventuallyProperty, UnboundedStrongRangeBeginsAfterItsMinimum) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      EventuallySource("  p: assert property (@(posedge clk) s_eventually "
                       "[2:$] a) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 0u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 3u);
}

constexpr const char* kPlacedStimulus =
    "  assign a = tick inside {1, 3};\n"
    "  assign b = tick inside {2, 3};\n"
    "  assign c = tick inside {2, 4};\n"
    "  assign d = tick inside {1, 2, 3};\n";

constexpr const char* kPlacedDeclarations =
    "  property q(x, y); x |-> y; endproperty\n";

const PlacedProperty kPlacedProperties[] = {
    {"s_eventually c", {4, 0}, 4},
    {"s_eventually a", {3, 1}, 3},
    {"eventually [0:1] !d", {2, 2}, 2},
    {"s_eventually [0:1] !d", {2, 2}, 2},
    {"eventually [1:2] a", {4, 0}, 4},
    {"s_eventually [1:2] a", {2, 2}, 2},
    {"eventually [0:0] b", {2, 2}, 2},
    {"s_eventually [0:0] b", {2, 2}, 2},
    {"s_eventually [2:$] c", {2, 2}, 2},
    {"s_eventually always c", {4, 0}, 4},
    {"s_eventually always d", {0, 4}, 0},
    {"always s_eventually c", {4, 0}, 4},
    {"always s_eventually a", {0, 4}, 0},
    {"a |-> s_eventually [1:2] b", {3, 1}, 3},
    {"s_eventually [1:1] q(a, c)", {2, 2}, 2},
    {"strong(##[0:$] a)", {3, 1}, 3},
    {"strong(##[1:2] a)", {2, 2}, 2}};

TEST(EventuallyProperty, AnEventuallyCountsInEachPlace) {
  for (const char* place : kPropertyPlaces) {
    for (const PlacedProperty& property : kPlacedProperties) {
      ExpectPropertyCountsInPlace(place, property, kPlacedStimulus,
                                  kPlacedDeclarations);
    }
  }
}

TEST(EventuallyProperty,
     DISABLED_AnEventuallyCountsInACompilationUnitProperty) {
  for (const PlacedProperty& property : kPlacedProperties) {
    ExpectPropertyCountsInPlace("unit", property, kPlacedStimulus,
                                kPlacedDeclarations);
  }
}

TEST(EventuallyProperty,
     DISABLED_TheWeakSequenceOfARangedWeakEventuallyCountsInEachPlace) {
  for (const char* place : kPropertyPlaces) {
    ExpectPropertyCountsInPlace(place, {"weak(##[1:2] a)", {4, 0}, 4},
                                kPlacedStimulus);
  }
}

TEST(EventuallyProperty, AnOffTickEventuallyFirstAlignsToItsClock) {
  EXPECT_EQ(SlowClockConsequentCounts("s_eventually [0:0] b"),
            (PlaceCounts{3, 1}));
  EXPECT_EQ(SlowClockConsequentCounts("s_eventually [1:1] b"),
            (PlaceCounts{2, 2}));
  EXPECT_EQ(SlowClockConsequentCounts("eventually [1:1] b"),
            (PlaceCounts{3, 1}));
  EXPECT_EQ(SlowClockConsequentCounts("s_eventually b"), (PlaceCounts{3, 1}));
  EXPECT_EQ(SlowClockConsequentCounts("eventually [0:1] b"),
            (PlaceCounts{4, 0}));
}

}  // namespace
