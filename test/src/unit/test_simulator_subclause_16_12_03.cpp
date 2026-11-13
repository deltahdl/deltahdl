#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_property_places.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sampling.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(NegationProperty, NotOfTrueIsFalse) {
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kPass), PropertyResult::kFail);
}

TEST(NegationProperty, NotOfFalseIsTrue) {
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kFail), PropertyResult::kPass);
}

TEST(NegationProperty, ComplementOfEveryUnderlyingVerdict) {
  EXPECT_EQ(EvalPropertyNot(EvalPropertyNot(PropertyResult::kPass)),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyNot(EvalPropertyNot(PropertyResult::kFail)),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kVacuousPass),
            PropertyResult::kFail);
}

TEST(NegationProperty, NegationMakesWeakStrong) {
  EXPECT_EQ(NegatePropertyStrength(SequencePropertyStrength::kWeak),
            SequencePropertyStrength::kStrong);
}

TEST(NegationProperty, NegationMakesStrongWeak) {
  EXPECT_EQ(NegatePropertyStrength(SequencePropertyStrength::kStrong),
            SequencePropertyStrength::kWeak);
}

std::string NegationSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic a, b, busy;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign a = tick inside {1, 2, 4};\n"
         "  assign b = tick inside {2};\n"
         "  assign busy = tick inside {3};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

TEST(NegationProperty, NotOfABooleanIsItsOpposite) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      NegationSource("  a1: assert property (@(posedge clk) not busy) "
                     "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  SimFixture g;
  auto* named = RunAndFindVar(
      NegationSource(
          "  property p_idle;\n"
          "    @(posedge clk) not busy;\n"
          "  endproperty\n"
          "  a2: assert property (p_idle) passes++; else fails++;\n"),
      g, "passes");
  ASSERT_NE(named, nullptr);
  EXPECT_EQ(named->value.ToUint64(), 3u);
  EXPECT_EQ(g.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

TEST(NegationProperty, NotOfAWeakSequenceFailsUnfinishedAtTheEnd) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      NegationSource("  a1: assert property (@(posedge clk) not a ##1 b) "
                     "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

TEST(NegationProperty, NotOfAStrongSequenceHoldsUnfinishedAtTheEnd) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      NegationSource("  a2: assert property (@(posedge clk) not strong(a ##1 "
                     "b)) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

TEST(NegationProperty, TwoNegationsCancel) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      NegationSource("  a1: assert property (@(posedge clk) not not busy) "
                     "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 3u);
}

constexpr const char* kPlacedStimulus =
    "  assign a = tick inside {1, 2, 4};\n  assign b = tick inside {2};\n  "
    "assign c = tick inside {3};\n";

constexpr const char* kPlacedDeclarations =
    "  property q(x, y); x |-> y; endproperty\n";

const PlacedProperty kPlacedProperties[] = {
    {"not c", {3, 1}, 3},
    {"not (a |-> b)", {2, 2}, 2},
    {"not weak(a ##1 b)", {2, 2}, 2},
    {"not not c", {1, 3}, 1},
    {"not (c |-> a)", {1, 3}, 1},
    {"not q(a, b)", {2, 2}, 2},
};

TEST(NegationProperty, ANegationCountsInEachPlace) {
  for (const char* place : kPropertyPlaces) {
    for (const PlacedProperty& property : kPlacedProperties) {
      ExpectPropertyCountsInPlace(place, property, kPlacedStimulus,
                                  kPlacedDeclarations);
    }
  }
}

TEST(NegationProperty, DISABLED_ANegationCountsInACompilationUnitProperty) {
  for (const PlacedProperty& property : kPlacedProperties) {
    ExpectPropertyCountsInPlace("unit", property, kPlacedStimulus,
                                kPlacedDeclarations);
  }
}

constexpr const char* kStoppedClock =
    "module t;\n"
    "  logic clk = 0, a = 0, b = 0;\n"
    "  int p1 = 0, f1 = 0, p2 = 0, f2 = 0;\n"
    "  a1: assert property (@clk not a ##1 b) p1++; else f1++;\n"
    "  a2: assert property (@clk not strong(a ##1 b)) p2++; else f2++;\n"
    "  initial begin\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0;\n"
    "    #2 a = 1;\n"
    "    #3 clk = 1;\n"
    "    #15 $finish;\n"
    "  end\n"
    "endmodule\n";

uint64_t Value(SimFixture& f, const char* name) {
  auto* variable = f.ctx.FindVariable(name);
  return variable == nullptr ? ~0ull : variable->value.ToUint64();
}

TEST(NegationProperty, TheNegatedWeakSequenceFailsWhenTheClockStops) {
  SimFixture f;
  RunAndFindVar(kStoppedClock, f, "p1");
  EXPECT_EQ(Value(f, "p1"), 2u);
  EXPECT_EQ(Value(f, "f1"), 0u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(Value(f, "p1"), 2u);
  EXPECT_EQ(Value(f, "f1"), 1u);
  EXPECT_EQ(Value(f, "f2"), 0u);
}

TEST(NegationProperty,
     DISABLED_TheNegatedStrongSequenceHoldsWhenTheClockStops) {
  SimFixture f;
  RunAndFindVar(kStoppedClock, f, "p2");
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(Value(f, "p2"), 3u);
  EXPECT_EQ(Value(f, "f2"), 0u);
}

}  // namespace
