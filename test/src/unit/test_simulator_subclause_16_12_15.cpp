#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_property_places.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string WeakStrongSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic a = 1, b = 0, c;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  int when = 0;\n"
         "  initial repeat (6) #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign c = tick inside {1, 2};\n" +
         items +
         "  initial #100 $finish;\n"
         "endmodule\n";
}

uint64_t FailsOf(const std::string& spec) {
  SimFixture f;
  auto* fails = RunAndFindVar(
      WeakStrongSource("  p: assert property (@(posedge clk) " + spec +
                       ") passes++; else begin fails++; when = $time; end\n"),
      f, "fails");
  if (fails == nullptr) return ~0ull;
  f.ctx.RunFinalBlocks();
  return fails->value.ToUint64();
}

TEST(WeakStrongOperators, NexttimeNeedsNoTickWhereSNexttimeDoes) {
  EXPECT_EQ(FailsOf("nexttime a"), 0u);
  EXPECT_EQ(FailsOf("s_nexttime a"), 1u);
}

TEST(WeakStrongOperators, AlwaysAndEventuallyHoldWhereTheStrongFormsFail) {
  EXPECT_EQ(FailsOf("always a"), 0u);
  EXPECT_EQ(FailsOf("s_always [0:3] a"), 3u);
  EXPECT_EQ(FailsOf("eventually [0:3] b"), 0u);
  EXPECT_EQ(FailsOf("s_eventually b"), 3u);
}

TEST(WeakStrongOperators, UntilAndWeakHoldWhereSUntilAndStrongFail) {
  EXPECT_EQ(FailsOf("a until b"), 0u);
  EXPECT_EQ(FailsOf("a s_until b"), 3u);
  EXPECT_EQ(FailsOf("a until_with b"), 0u);
  EXPECT_EQ(FailsOf("a s_until_with b"), 3u);
  EXPECT_EQ(FailsOf("weak(a ##1 a)"), 0u);
  EXPECT_EQ(FailsOf("strong(a ##1 a)"), 1u);
}

TEST(WeakStrongOperators, ASafetyPropertyFailsAtAFiniteTime) {
  SimFixture f;
  auto* fails = RunAndFindVar(
      WeakStrongSource("  p: assert property (@(posedge clk) always c) "
                       "passes++; else begin fails++; when = $time; end\n"),
      f, "fails");
  ASSERT_NE(fails, nullptr);
  EXPECT_EQ(fails->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("when")->value.ToUint64(), 25u);
}

constexpr const char* kPlacedStimulus =
    "  assign a = tick inside {1, 3};\n"
    "  assign b = tick inside {2, 3};\n"
    "  assign c = tick inside {2, 4};\n"
    "  assign d = tick inside {1, 2, 3};\n";

const PlacedProperty kWeakAndStrongPairs[] = {
    {"nexttime c", {3, 1}, 3},         {"s_nexttime c", {2, 2}, 2},
    {"always [1:2] b", {2, 2}, 2},     {"s_always [1:2] b", {1, 3}, 1},
    {"eventually [1:2] a", {4, 0}, 4}, {"s_eventually [1:2] a", {2, 2}, 2},
    {"c until a", {4, 0}, 4},          {"c s_until a", {3, 1}, 3},
    {"c until_with a", {1, 3}, 1},     {"c s_until_with a", {0, 4}, 0},
    {"strong(c ##1 1)", {1, 3}, 1}};

TEST(WeakStrongOperators, AnAttemptOpenAtTheEndCountsInEachPlace) {
  for (const char* place : kPropertyPlaces) {
    for (const PlacedProperty& property : kWeakAndStrongPairs) {
      ExpectPropertyCountsInPlace(place, property, kPlacedStimulus);
    }
  }
}

TEST(WeakStrongOperators, DISABLED_AnOpenWeakSequenceAttemptHoldsInEachPlace) {
  for (const char* place : kPropertyPlaces) {
    ExpectPropertyCountsInPlace(place, {"weak(c ##1 1)", {2, 2}, 2},
                                kPlacedStimulus);
  }
}

TEST(WeakStrongOperators,
     DISABLED_AnAttemptOpenAtTheEndCountsInACompilationUnitProperty) {
  for (const PlacedProperty& property : kWeakAndStrongPairs) {
    ExpectPropertyCountsInPlace("unit", property, kPlacedStimulus);
  }
}

}  // namespace
