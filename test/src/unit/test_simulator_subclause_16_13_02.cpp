#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_property_places.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string MulticlockPropertySource(const std::string& items) {
  return "module t;\n"
         "  logic clk0 = 0;\n"
         "  logic clk1 = 0;\n"
         "  logic clk2 = 0;\n"
         "  int tick = 1;\n"
         "  logic sig0, sig1, b, s1, s2;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  int pass_sum = 0;\n"
         "  always #5 clk0 = ~clk0;\n"
         "  always #10 tick = tick + 1;\n"
         "  initial begin\n"
         "    #12 clk1 = 1; #8 clk1 = 0; #7 clk1 = 1; #8 clk1 = 0;\n"
         "    #10 clk1 = 1; #5 clk1 = 0; #7 clk1 = 1; #8 clk1 = 0;\n"
         "    #7 clk1 = 1; #6 clk1 = 0;\n"
         "  end\n"
         "  initial begin\n"
         "    #8 clk2 = 1; #8 clk2 = 0; #9 clk2 = 1; #7 clk2 = 0;\n"
         "    #6 clk2 = 1; #8 clk2 = 0; #9 clk2 = 1; #7 clk2 = 0;\n"
         "    #8 clk2 = 1; #4 clk2 = 0; #4 clk2 = 1; #1 clk2 = 0;\n"
         "  end\n"
         "  assign sig0 = tick inside {1, 2, 5, 7};\n"
         "  assign sig1 = tick inside {3, 5};\n"
         "  assign b = tick inside {1, 3, 6};\n"
         "  assign s1 = tick inside {2, 3};\n"
         "  assign s2 = tick inside {4, 7};\n" +
         items +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

struct MulticlockPropertyCounts {
  uint64_t passes;
  uint64_t fails;
  uint64_t pass_sum;
};

MulticlockPropertyCounts CountsOfMulticlockProperty(const std::string& spec) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      MulticlockPropertySource("  p: assert property (@(posedge clk0) " + spec +
                               ") begin passes++; pass_sum += $time; end "
                               "else fails++;\n"),
      f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull, ~0ull};
  Variable* fails = f.ctx.FindVariable("fails");
  Variable* pass_sum = f.ctx.FindVariable("pass_sum");
  return {passes->value.ToUint64(), fails->value.ToUint64(),
          pass_sum->value.ToUint64()};
}

TEST(MulticlockedProperty, AnAndOfClockedOperandsNeedsBothMatchesFromThePoint) {
  MulticlockPropertyCounts counts = CountsOfMulticlockProperty(
      "1 |-> (@(posedge clk0) sig0) and (@(posedge clk1) sig1)");
  EXPECT_EQ(counts.passes, 2u);
  EXPECT_EQ(counts.fails, 6u);
  EXPECT_EQ(counts.pass_sum, 72u);
}

TEST(MulticlockedProperty,
     NonoverlappingImplicationAwaitsTheNextTickOfTheConsequentClock) {
  MulticlockPropertyCounts counts =
      CountsOfMulticlockProperty("sig0 |=> @(posedge clk1) sig1");
  EXPECT_EQ(counts.passes, 5u);
  EXPECT_EQ(counts.fails, 3u);
  EXPECT_EQ(counts.pass_sum, 217u);
}

TEST(MulticlockedProperty,
     OverlappingImplicationChecksAtACoincidentTickAtOnce) {
  MulticlockPropertyCounts counts =
      CountsOfMulticlockProperty("sig0 |-> @(posedge clk1) sig1");
  EXPECT_EQ(counts.passes, 6u);
  EXPECT_EQ(counts.fails, 2u);
  EXPECT_EQ(counts.pass_sum, 262u);
}

TEST(MulticlockedProperty, IfElseReadsEachBranchAtItsClocksNearestTick) {
  MulticlockPropertyCounts counts = CountsOfMulticlockProperty(
      "if (b) @(posedge clk1) s1 else @(posedge clk2) s2");
  EXPECT_EQ(counts.passes, 4u);
  EXPECT_EQ(counts.fails, 4u);
  EXPECT_EQ(counts.pass_sum, 147u);
}

TEST(MulticlockedProperty, SequenceAsPropertyIsTrueIffMatch) {
  EXPECT_EQ(EvalMulticlockedSequenceAsProperty(true), PropertyResult::kPass);
  EXPECT_EQ(EvalMulticlockedSequenceAsProperty(false), PropertyResult::kFail);

  EXPECT_NE(EvalMulticlockedSequenceAsProperty(true), PropertyResult::kPending);
  EXPECT_NE(EvalMulticlockedSequenceAsProperty(false),
            PropertyResult::kPending);
}

TEST(MulticlockedProperty, BooleanAndRequiresBothOperandMatches) {
  EXPECT_EQ(EvalMulticlockedAnd(true, true), PropertyResult::kPass);
  EXPECT_EQ(EvalMulticlockedAnd(true, false), PropertyResult::kFail);
  EXPECT_EQ(EvalMulticlockedAnd(false, true), PropertyResult::kFail);
  EXPECT_EQ(EvalMulticlockedAnd(false, false), PropertyResult::kFail);
}

TEST(MulticlockedProperty, NonOverlappingAdvancesToStrictlyFutureTick) {
  const std::vector<uint64_t> kConsequentTicks = {10, 20, 30};
  EXPECT_EQ(MulticlockedConsequentEvalTick(20, kConsequentTicks, false), 30u);
  EXPECT_FALSE(
      MulticlockedImplicationChecksImmediately(20, kConsequentTicks, false));
}

TEST(MulticlockedProperty, NonOverlappingHasNoTickPastTheEnd) {
  const std::vector<uint64_t> kConsequentTicks = {10, 20};
  EXPECT_EQ(MulticlockedConsequentEvalTick(20, kConsequentTicks, false),
            kNoMulticlockTick);
}

TEST(MulticlockedProperty, OverlappingChecksImmediatelyOnCoincidentTick) {
  const std::vector<uint64_t> kConsequentTicks = {10, 20, 30};
  EXPECT_EQ(MulticlockedConsequentEvalTick(20, kConsequentTicks, true), 20u);
  EXPECT_TRUE(
      MulticlockedImplicationChecksImmediately(20, kConsequentTicks, true));
}

TEST(MulticlockedProperty, OverlappingWithoutCoincidentTickActsNonOverlapping) {
  const std::vector<uint64_t> kConsequentTicks = {10, 25, 30};
  EXPECT_EQ(MulticlockedConsequentEvalTick(20, kConsequentTicks, true), 25u);
  EXPECT_FALSE(
      MulticlockedImplicationChecksImmediately(20, kConsequentTicks, true));
}

TEST(MulticlockedProperty, ImplicationConsequentIsMulticlockedAnd) {
  const std::vector<uint64_t> kClk1Ticks = {15, 25};
  const uint64_t kEvalTick =
      MulticlockedConsequentEvalTick(10, kClk1Ticks, false);
  EXPECT_EQ(kEvalTick, 15u);

  EXPECT_EQ(EvalMulticlockedAnd(true, true), PropertyResult::kPass);
  EXPECT_EQ(EvalMulticlockedAnd(true, false), PropertyResult::kFail);
}

TEST(MulticlockedProperty, IfThenBranchAllowsOverlappingTick) {
  const std::vector<uint64_t> kThenTicks = {12, 18, 24};
  EXPECT_EQ(MulticlockedIfBranchEvalTick(12, kThenTicks), 12u);
}

TEST(MulticlockedProperty, IfElseBranchTakesNearestNonStrictlySubsequentTick) {
  const std::vector<uint64_t> kElseTicks = {10, 22, 33};
  EXPECT_EQ(MulticlockedIfBranchEvalTick(15, kElseTicks), 22u);
}

TEST(MulticlockedProperty, IfElseBranchAdmitsCoincidentTick) {
  const std::vector<uint64_t> kElseTicks = {15, 22, 33};
  EXPECT_EQ(MulticlockedIfBranchEvalTick(15, kElseTicks), 15u);
}

TEST(MulticlockedProperty, IfElseRoutesByCondition) {
  EXPECT_EQ(EvalPropertyIfElse(true, PropertyResult::kPass, true,
                               PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyIfElse(false, PropertyResult::kPass, true,
                               PropertyResult::kFail),
            PropertyResult::kFail);
}

TEST(MulticlockedProperty, NoClockTicksYieldsSentinel) {
  const std::vector<uint64_t> kNoTicks = {};
  EXPECT_EQ(NearestClockTickAtOrAfter(0, kNoTicks, true), kNoMulticlockTick);
  EXPECT_EQ(NearestClockTickAtOrAfter(0, kNoTicks, false), kNoMulticlockTick);
}

TEST(MulticlockedProperty, ConsequentTickWhenAntecedentEndsBeforeFirstTick) {
  const std::vector<uint64_t> kConsequentTicks = {10, 20};
  EXPECT_EQ(MulticlockedConsequentEvalTick(3, kConsequentTicks, false), 10u);
  EXPECT_EQ(MulticlockedConsequentEvalTick(3, kConsequentTicks, true), 10u);
  EXPECT_FALSE(
      MulticlockedImplicationChecksImmediately(3, kConsequentTicks, true));
}

TEST(MulticlockedProperty, OverlappingImplicationHasNoTickFromTheEnd) {
  const std::vector<uint64_t> kConsequentTicks = {5, 10};
  EXPECT_EQ(MulticlockedConsequentEvalTick(15, kConsequentTicks, true),
            kNoMulticlockTick);
  EXPECT_FALSE(
      MulticlockedImplicationChecksImmediately(15, kConsequentTicks, true));
}

TEST(MulticlockedProperty, IfBranchHasNoTickFromCondition) {
  const std::vector<uint64_t> kBranchTicks = {10, 20, 30};
  EXPECT_EQ(MulticlockedIfBranchEvalTick(40, kBranchTicks), kNoMulticlockTick);
}

constexpr const char* kMulticlockStimulus =
    "  assign a = tick inside {1, 3};\n"
    "  initial begin b = 1; #8 b = 0; #4 b = 1; #10 b = 0; #5 b = 1; #5 b = 0; "
    "end\n"
    "  assign c = tick inside {1, 2, 3};\n"
    "  assign d = tick == 1;\n";

constexpr const char* kMulticlockPlaces[] = {
    "module",  "generate",        "interface",          "program",
    "checker", "module property", "interface property", "checker property"};

std::string MulticlockPlaceSource(const std::string& place,
                                  const std::string& directive,
                                  const std::string& body) {
  if (place.ends_with(" property") && place != "module property") {
    std::string unit = place.substr(0, place.size() - 9);
    std::string items = "  property P; @(posedge clk) " + body +
                        "; endproperty\n" + PlacedDirective(directive, "P");
    std::string header = unit == "checker"
                             ? "checker w(clk, a, b, c, d);\n"
                             : unit + " w(input logic clk, a, b, c, d);\n";
    return header + items + "end" + unit + "\n" +
           PlacedTop(kMulticlockStimulus, "  w u(clk, a, b, c, d);\n");
  }
  return ClockedPlaceSource(place, directive, body, kMulticlockStimulus);
}

template <typename Places, typename Rows>
void ExpectMulticlockCountsIn(const Places& places, const Rows& rows) {
  ExpectCountsInEachPlace(places, rows, MulticlockPlaceSource);
}

template <typename Rows>
void ExpectMulticlockCountsInEachPlace(const Rows& rows) {
  ExpectMulticlockCountsIn(kMulticlockPlaces, rows);
  ExpectMulticlockCountsIn(kDefaultClockedPlaces, rows);
}

constexpr PlacedProperty kImplicationsAcrossClocks[] = {
    {"a |=> @(negedge clk) b", {3, 1}, 3},
    {"d |=> @(negedge clk) b", {3, 1}, 3},
    {"d |=> @(clk) b", {3, 1}, 3},
    {"d |-> @(negedge clk) b", {3, 1}, 3},
    {"a && !d |-> @(clk) b", {3, 1}, 3},
    {"a ##1 b |=> @(negedge clk) !b", {3, 1}, 3},
    {"d |=> @(negedge clk) !b ##2 b", {4, 0}, 4},
    {"d ##1 @(negedge clk) !b ##2 b", {1, 3}, 1}};

constexpr PlacedProperty kBooleansAcrossClocks[] = {
    {"c |-> (@(posedge clk) a) and (@(negedge clk) b)", {2, 2}, 2},
    {"a && !d |-> (@(posedge clk) a) and (@(clk) !b)", {4, 0}, 4},
    {"c |-> (@(posedge clk) !a) or (@(negedge clk) b)", {3, 1}, 3},
    {"d |-> (@(posedge clk) !a) or (@(negedge clk) b)", {3, 1}, 3},
    {"d |-> not (@(negedge clk) b)", {4, 0}, 4},
    {"c |-> not (@(negedge clk) b)", {2, 2}, 2},
    {"a && !d |-> not (@(clk) b)", {4, 0}, 4},
    {"c |-> (@(negedge clk) b) implies (@(posedge clk) a)", {3, 1}, 3},
    {"d |-> (@(posedge clk) a) implies (@(clk) b)", {4, 0}, 4},
    {"d |-> (@(posedge clk) a) iff (@(clk) b)", {4, 0}, 4},
    {"d |-> (@(posedge clk) a) and (@(negedge clk) !b ##2 b)", {4, 0}, 4},
    {"d |-> (@(posedge clk) !a) or (@(negedge clk) !b ##2 b)", {4, 0}, 4},
    {"d |-> not (@(negedge clk) !b ##2 b)", {3, 1}, 3}};

constexpr PlacedProperty kIfsAcrossClocks[] = {
    {"if (a) @(negedge clk) b", {3, 1}, 3},
    {"if (a && !d) @(clk) !b", {4, 0}, 4},
    {"if (d) @(negedge clk) !b ##2 b", {4, 0}, 4},
    {"if (a) @(negedge clk) b else @(clk) !b", {2, 2}, 2},
    {"if (!a || d) 1 else @(clk) !b", {4, 0}, 4}};

constexpr PlacedProperty kImpliesAndIffAcrossClocks[] = {
    {"c |-> (@(posedge clk) a) implies (@(negedge clk) b)", {3, 1}, 3},
    {"c |-> (@(posedge clk) a) iff (@(negedge clk) b)", {2, 2}, 2},
    {"d |-> (@(posedge clk) a) iff (@(negedge clk) b)", {3, 1}, 3},
    {"d |-> (@(posedge clk) a) implies (@(negedge clk) !b ##2 b)", {4, 0}, 4},
    {"d |-> (@(posedge clk) a) iff (@(negedge clk) !b ##2 b)", {4, 0}, 4}};

constexpr PlacedProperty kBooleanConsequentsOfNonoverlapping[] = {
    {"d |=> (@(negedge clk) !b) and (@(posedge clk) b)", {4, 0}, 4},
    {"d |=> (@(negedge clk) b) and (@(posedge clk) b)", {3, 1}, 3},
    {"a |=> (@(negedge clk) !b) and (@(posedge clk) b)", {3, 1}, 3},
    {"d |=> (@(negedge clk) b) or (@(posedge clk) !b)", {3, 1}, 3},
    {"d |=> not (@(negedge clk) b)", {4, 0}, 4},
    {"d |=> (@(posedge clk) b) implies (@(negedge clk) b)", {3, 1}, 3},
    {"d |=> (@(posedge clk) b) iff (@(negedge clk) b)", {3, 1}, 3}};

constexpr PlacedProperty kFirstTicksInTheAttemptsTimeStep[] = {
    {"d |-> @(clk) b", {4, 0}, 4},
    {"a |-> @(clk) b", {3, 1}, 3},
    {"d |-> (@(posedge clk) !a) or (@(clk) b)", {4, 0}, 4},
    {"d |-> not (@(clk) b)", {3, 1}, 3},
    {"if (d) @(clk) b", {4, 0}, 4},
    {"if (d) @(clk) b else a", {2, 2}, 2},
    {"if (!d) a else @(clk) b", {2, 2}, 2},
    {"d ##0 @(clk) b", {1, 3}, 1}};

TEST(MulticlockedPropertyRun,
     AnImplicationAwaitsTheConsequentClocksNearestTickInEachPlace) {
  ExpectMulticlockCountsInEachPlace(kImplicationsAcrossClocks);
}

TEST(MulticlockedPropertyRun,
     ABooleanOperatorReadsEachOperandOnItsOwnClockInEachPlace) {
  ExpectMulticlockCountsInEachPlace(kBooleansAcrossClocks);
}

TEST(MulticlockedPropertyRun,
     AnIfReadsItsBranchAtTheBranchClocksNearestTickInEachPlace) {
  ExpectMulticlockCountsInEachPlace(kIfsAcrossClocks);
}

TEST(MulticlockedPropertyRun,
     DISABLED_ImpliesAndIffReadTheOtherClocksOperandAtItsNearestTick) {
  ExpectMulticlockCountsInEachPlace(kImpliesAndIffAcrossClocks);
}

TEST(MulticlockedPropertyRun,
     DISABLED_ANonoverlappingConsequentStartsEachOperandAtItsClocksNextTick) {
  ExpectMulticlockCountsInEachPlace(kBooleanConsequentsOfNonoverlapping);
}

TEST(MulticlockedPropertyRun,
     DISABLED_AClocksFirstTickInTheAttemptsTimeStepIsCoincident) {
  ExpectMulticlockCountsInEachPlace(kFirstTicksInTheAttemptsTimeStep);
}

template <typename Places>
void ExpectEveryAcceptedRowIn(const Places& places) {
  ExpectMulticlockCountsIn(places, kImplicationsAcrossClocks);
  ExpectMulticlockCountsIn(places, kBooleansAcrossClocks);
  ExpectMulticlockCountsIn(places, kIfsAcrossClocks);
}

TEST(MulticlockedPropertyRun,
     DISABLED_AMulticlockedPropertyCountsInAClockedProcedure) {
  ExpectEveryAcceptedRowIn(
      std::initializer_list<const char*>{"clocked procedural"});
}

TEST(MulticlockedPropertyRun,
     DISABLED_AMulticlockedPropertyCountsInAPackageProperty) {
  ExpectEveryAcceptedRowIn(
      std::initializer_list<const char*>{"package property"});
}

TEST(MulticlockedPropertyRun,
     DISABLED_AMulticlockedPropertyCountsInACompilationUnitProperty) {
  ExpectEveryAcceptedRowIn(std::initializer_list<const char*>{"unit"});
}

}  // namespace
