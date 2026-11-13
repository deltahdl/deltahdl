#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_property_places.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PropertyConjunction, BothOperandsPass) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);
}

TEST(PropertyConjunction, VacuousOperandStillHolds) {
  EXPECT_EQ(
      EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kVacuousPass),
      PropertyResult::kPass);
}

TEST(PropertyConjunction, LeftOperandFails) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kFail);
}

TEST(PropertyConjunction, RightOperandFails) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kFail);
}

TEST(PropertyConjunction, BothOperandsFail) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kFail);
}

TEST(PropertyConjunction, BothOperandsVacuous) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kVacuousPass,
                            PropertyResult::kVacuousPass),
            PropertyResult::kPass);
}

TEST(PropertyConjunction, FailDominatesVacuousLeft) {
  EXPECT_EQ(
      EvalPropertyAnd(PropertyResult::kFail, PropertyResult::kVacuousPass),
      PropertyResult::kFail);
}

TEST(PropertyConjunction, FailDominatesVacuousRight) {
  EXPECT_EQ(
      EvalPropertyAnd(PropertyResult::kVacuousPass, PropertyResult::kFail),
      PropertyResult::kFail);
}

TEST(PropertyConjunction, VacuousWithPassHolds) {
  EXPECT_EQ(
      EvalPropertyAnd(PropertyResult::kVacuousPass, PropertyResult::kPass),
      PropertyResult::kPass);
}

std::string ConjunctionSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic a, b, c, d;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign a = tick inside {1, 4};\n"
         "  assign b = tick inside {1, 2};\n"
         "  assign c = tick inside {2, 3};\n"
         "  assign d = tick inside {1, 4};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

TEST(PropertyConjunction, BooleanOperandsHoldWhereBothDo) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ConjunctionSource("  p: assert property (@(posedge clk) a and b) "
                        "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 3u);
}

TEST(PropertyConjunction, SequenceOperandDecidesWhereItMatchesOrCannot) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ConjunctionSource("  p: assert property (@(posedge clk) (a ##1 c) and d) "
                        "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

TEST(PropertyConjunction, StrongSequenceOperandFailsUnfinishedAtTheEnd) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ConjunctionSource("  p: assert property (@(posedge clk) strong(a ##1 c) "
                        "and d) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 3u);
  SimFixture g;
  auto* early = RunAndFindVar(
      ConjunctionSource("  p: assert property (@(posedge clk) (a ##1 c) and b) "
                        "passes++; else fails++;\n"),
      g, "passes");
  ASSERT_NE(early, nullptr);
  EXPECT_EQ(early->value.ToUint64(), 1u);
  EXPECT_EQ(g.ctx.FindVariable("fails")->value.ToUint64(), 3u);
}

TEST(PropertyConjunction, AndBindsTighterThanOr) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ConjunctionSource("  p: assert property (@(posedge clk) a or b and c) "
                        "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

constexpr const char* kPlacedStimulus =
    "  assign a = tick inside {1, 4};\n  assign b = tick inside {1, 2};\n  "
    "assign c = tick inside {2, 3};\n  assign d = tick inside {1, 4};\n";

constexpr const char* kPlacedDeclarations =
    "  property q(x, y); x |-> y; endproperty\n";

const PlacedProperty kPlacedProperties[] = {
    {"a and b", {1, 3}, 1},
    {"(b |-> c) and (a or c)", {3, 1}, 3},
    {"(a ##1 c) and d", {2, 2}, 1},
    {"strong(a ##1 c) and d", {1, 3}, 1},
    {"q(b, c) and (a or c)", {3, 1}, 3},
};

TEST(PropertyConjunction, AConjunctionCountsInEachPlace) {
  for (const char* place : kPropertyPlaces) {
    for (const PlacedProperty& property : kPlacedProperties) {
      ExpectPropertyCountsInPlace(place, property, kPlacedStimulus,
                                  kPlacedDeclarations);
    }
  }
}

TEST(PropertyConjunction,
     DISABLED_AConjunctionCountsInACompilationUnitProperty) {
  for (const PlacedProperty& property : kPlacedProperties) {
    ExpectPropertyCountsInPlace("unit", property, kPlacedStimulus,
                                kPlacedDeclarations);
  }
}

TEST(PropertyConjunction,
     DISABLED_AParenthesizedConjunctionOfBooleansCountsInEachPlace) {
  const PlacedProperty kParenthesized[] = {{"(a and b)", {1, 3}, 1},
                                           {"((a and b))", {1, 3}, 1},
                                           {"not (a and b)", {3, 1}, 3}};
  for (const char* place : kPropertyPlaces) {
    for (const PlacedProperty& property : kParenthesized) {
      ExpectPropertyCountsInPlace(place, property, kPlacedStimulus);
    }
  }
}

}  // namespace
