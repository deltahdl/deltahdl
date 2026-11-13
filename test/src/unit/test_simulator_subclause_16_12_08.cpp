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

TEST(SvaEngine, PropertyNot) {
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kPass), PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kFail), PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kVacuousPass),
            PropertyResult::kFail);
}

TEST(SvaEngine, PropertyImplies) {
  EXPECT_EQ(EvalPropertyImplies(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyImplies(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyImplies(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyImplies(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kPass);
}

TEST(SvaEngine, PropertyIff) {
  EXPECT_EQ(EvalPropertyIff(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyIff(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyIff(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyIff(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kFail);
}

TEST(SvaEngine, ImpliesIffTreatVacuousPassAsHolding) {
  EXPECT_EQ(
      EvalPropertyImplies(PropertyResult::kVacuousPass, PropertyResult::kFail),
      PropertyResult::kFail);
  EXPECT_EQ(
      EvalPropertyImplies(PropertyResult::kPass, PropertyResult::kVacuousPass),
      PropertyResult::kPass);
  EXPECT_EQ(
      EvalPropertyImplies(PropertyResult::kFail, PropertyResult::kVacuousPass),
      PropertyResult::kPass);
  EXPECT_EQ(
      EvalPropertyIff(PropertyResult::kVacuousPass, PropertyResult::kPass),
      PropertyResult::kPass);
  EXPECT_EQ(
      EvalPropertyIff(PropertyResult::kVacuousPass, PropertyResult::kFail),
      PropertyResult::kFail);
  EXPECT_EQ(
      EvalPropertyIff(PropertyResult::kPass, PropertyResult::kVacuousPass),
      PropertyResult::kPass);
  EXPECT_EQ(
      EvalPropertyIff(PropertyResult::kFail, PropertyResult::kVacuousPass),
      PropertyResult::kFail);
}

std::string ImpliesSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic a, b, c;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign a = tick inside {1, 3};\n"
         "  assign b = tick inside {2, 3};\n"
         "  assign c = tick inside {2, 3};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

TEST(ImpliesIffProperty, ImpliesHoldsWhereTheFirstIsFalseOrTheSecondTrue) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ImpliesSource("  p: assert property (@(posedge clk) a implies b) "
                    "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

TEST(ImpliesIffProperty, IffHoldsWhereBothAreAlike) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ImpliesSource("  p: assert property (@(posedge clk) a iff b) passes++; "
                    "else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

TEST(ImpliesIffProperty, IffBindsTighterThanImplies) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ImpliesSource("  p: assert property (@(posedge clk) a iff b implies c) "
                    "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

TEST(ImpliesIffProperty, ASequenceOperandIsDecidedWhereItMatchesOrCannot) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ImpliesSource("  p: assert property (@(posedge clk) (a ##1 b) implies "
                    "c) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

constexpr const char* kPlacedStimulus =
    "  assign a = tick inside {1, 3};\n"
    "  assign b = tick inside {2, 3};\n"
    "  assign c = tick inside {2, 4};\n"
    "  assign d = tick inside {1, 2, 3};\n";

constexpr const char* kPlacedDeclarations =
    "  property q(x, y); x |-> y; endproperty\n";

const PlacedProperty kPlacedProperties[] = {{"a implies c", {2, 2}, 2},
                                            {"a iff b", {2, 2}, 2},
                                            {"a iff c", {0, 4}, 0},
                                            {"a ##1 b implies c", {3, 1}, 3},
                                            {"a implies b ##1 c", {3, 1}, 3},
                                            {"(a |-> b) iff d", {2, 2}, 2},
                                            {"q(d, b) implies c", {3, 1}, 3},
                                            {"a iff q(d, b)", {1, 3}, 1},
                                            {"a ##1 b iff b ##1 c", {2, 2}, 2}};

TEST(ImpliesIffProperty, ImpliesAndIffCountInEachPlace) {
  for (const char* place : kPropertyPlaces) {
    for (const PlacedProperty& property : kPlacedProperties) {
      ExpectPropertyCountsInPlace(place, property, kPlacedStimulus,
                                  kPlacedDeclarations);
    }
  }
}

TEST(ImpliesIffProperty,
     DISABLED_ImpliesAndIffCountInACompilationUnitProperty) {
  for (const PlacedProperty& property : kPlacedProperties) {
    ExpectPropertyCountsInPlace("unit", property, kPlacedStimulus,
                                kPlacedDeclarations);
  }
}

}  // namespace
