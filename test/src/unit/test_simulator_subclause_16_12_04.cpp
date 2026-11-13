#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_property_places.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PropertyDisjunction, BothOperandsPass) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);
}

TEST(PropertyDisjunction, LeftOperandPasses) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kPass);
}

TEST(PropertyDisjunction, RightOperandPasses) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kPass);
}

TEST(PropertyDisjunction, BothOperandsFail) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kFail);
}

TEST(PropertyDisjunction, VacuousLeftStillHolds) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kVacuousPass, PropertyResult::kFail),
            PropertyResult::kPass);
}

TEST(PropertyDisjunction, VacuousRightStillHolds) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kVacuousPass),
            PropertyResult::kPass);
}

std::string DisjunctionSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic a, b, c;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign a = tick inside {1, 4};\n"
         "  assign b = tick inside {2};\n"
         "  assign c = tick inside {3};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

TEST(PropertyDisjunction, BooleanOperandsHoldWhereEitherDoes) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      DisjunctionSource("  p: assert property (@(posedge clk) a or b) "
                        "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

TEST(PropertyDisjunction, SequenceOperandDecidesWhereItMatchesOrCannot) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      DisjunctionSource("  p: assert property (@(posedge clk) (a ##1 b) or c) "
                        "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

TEST(PropertyDisjunction, StrongSequenceOperandFailsUnfinishedAtTheEnd) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      DisjunctionSource("  p: assert property (@(posedge clk) strong(a ##1 b) "
                        "or c) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

TEST(PropertyDisjunction, NotBindsTighterThanOr) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      DisjunctionSource("  p: assert property (@(posedge clk) not a or b) "
                        "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

constexpr const char* kPlacedStimulus =
    "  assign a = tick inside {1, 4};\n  assign b = tick inside {2};\n  assign "
    "c = tick inside {3};\n";

constexpr const char* kPlacedDeclarations =
    "  property q(x, y); x |-> y; endproperty\n";

const PlacedProperty kPlacedProperties[] = {
    {"a or b", {3, 1}, 3},         {"(a |-> b) or c", {2, 2}, 2},
    {"(a ##1 b) or c", {3, 1}, 2}, {"strong(a ##1 b) or c", {2, 2}, 2},
    {"not a or b", {2, 2}, 2},     {"q(a, b) or c", {2, 2}, 2},
};

TEST(PropertyDisjunction, ADisjunctionCountsInEachPlace) {
  for (const char* place : kPropertyPlaces) {
    for (const PlacedProperty& property : kPlacedProperties) {
      ExpectPropertyCountsInPlace(place, property, kPlacedStimulus,
                                  kPlacedDeclarations);
    }
  }
}

TEST(PropertyDisjunction,
     DISABLED_ADisjunctionCountsInACompilationUnitProperty) {
  for (const PlacedProperty& property : kPlacedProperties) {
    ExpectPropertyCountsInPlace("unit", property, kPlacedStimulus,
                                kPlacedDeclarations);
  }
}

TEST(PropertyDisjunction,
     DISABLED_AParenthesizedDisjunctionOfBooleansCountsInEachPlace) {
  const PlacedProperty kParenthesized[] = {{"(a or b)", {3, 1}, 3},
                                           {"((a or b))", {3, 1}, 3},
                                           {"not (b or c)", {2, 2}, 2}};
  for (const char* place : kPropertyPlaces) {
    for (const PlacedProperty& property : kParenthesized) {
      ExpectPropertyCountsInPlace(place, property, kPlacedStimulus);
    }
  }
}

}  // namespace
