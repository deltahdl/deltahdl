#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_property_places.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PropertyIfElse, SingleBranchGuardTrueTakesThen) {
  EXPECT_EQ(EvalPropertyIfElse(true, PropertyResult::kPass, false,
                               PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyIfElse(true, PropertyResult::kFail, false,
                               PropertyResult::kPass),
            PropertyResult::kFail);
}

TEST(PropertyIfElse, SingleBranchGuardFalseHoldsVacuously) {
  EXPECT_EQ(EvalPropertyIfElse(false, PropertyResult::kFail, false,
                               PropertyResult::kPass),
            PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalPropertyIfElse(false, PropertyResult::kPass, false,
                               PropertyResult::kPass),
            PropertyResult::kVacuousPass);
}

TEST(PropertyIfElse, TwoBranchGuardTrueTakesThen) {
  EXPECT_EQ(EvalPropertyIfElse(true, PropertyResult::kPass, true,
                               PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyIfElse(true, PropertyResult::kFail, true,
                               PropertyResult::kPass),
            PropertyResult::kFail);
}

TEST(PropertyIfElse, TwoBranchGuardFalseTakesElse) {
  EXPECT_EQ(EvalPropertyIfElse(false, PropertyResult::kFail, true,
                               PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyIfElse(false, PropertyResult::kPass, true,
                               PropertyResult::kFail),
            PropertyResult::kFail);
}

TEST(PropertyIfElse, SelectedBranchVacuousResultPropagates) {
  EXPECT_EQ(EvalPropertyIfElse(true, PropertyResult::kVacuousPass, true,
                               PropertyResult::kFail),
            PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalPropertyIfElse(false, PropertyResult::kFail, true,
                               PropertyResult::kVacuousPass),
            PropertyResult::kVacuousPass);
}

TEST(PropertyIfElse, SelectedBranchPendingResultPropagates) {
  EXPECT_EQ(EvalPropertyIfElse(true, PropertyResult::kPending, true,
                               PropertyResult::kPass),
            PropertyResult::kPending);
  EXPECT_EQ(EvalPropertyIfElse(false, PropertyResult::kPass, true,
                               PropertyResult::kPending),
            PropertyResult::kPending);
}

std::string IfElseSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic req, gnt, done, idle;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign req = tick inside {1, 2, 4};\n"
         "  assign gnt = tick inside {1, 4};\n"
         "  assign done = tick inside {2};\n"
         "  assign idle = tick inside {1};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

TEST(PropertyIfElse, FirstFormHoldsWhereTheConditionIsFalseOrTheBranchTrue) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      IfElseSource("  p: assert property (@(posedge clk) if (req) gnt) "
                   "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

TEST(PropertyIfElse, SecondFormTakesTheElseBranchWhereTheConditionIsFalse) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      IfElseSource("  p: assert property (@(posedge clk) if (req) gnt else "
                   "idle) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

TEST(PropertyIfElse, ASequenceBranchIsDecidedWhereItMatchesOrCannot) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      IfElseSource("  p: assert property (@(posedge clk) if (req) gnt ##1 "
                   "done else idle) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(passes->value.ToUint64(), 2u);
}

TEST(PropertyIfElse, IfElseBindsLoosest) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      IfElseSource("  p: assert property (@(posedge clk) if (req) gnt and "
                   "idle) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

constexpr const char* kPlacedStimulus =
    "  assign a = tick inside {1, 2, 4};\n"
    "  assign b = tick inside {1, 4};\n"
    "  assign c = tick inside {2};\n"
    "  assign d = tick inside {1};\n";

constexpr const char* kPlacedDeclarations =
    "  property q(x, y); x |-> y; endproperty\n";

const PlacedProperty kPlacedProperties[] = {
    {"if (a) b", {3, 1}, 3},
    {"if (a) b else d", {2, 2}, 2},
    {"if (a) b ##1 c else d", {2, 2}, 1},
    {"if (a) (b |-> c) else not c", {2, 2}, 2},
    {"if (a) q(c, b) else not c", {3, 1}, 3},
    {"if (a && !b) c else d", {2, 2}, 2},
    {"if (b dist {1 := 1}) a else d", {2, 2}, 2},
};

TEST(PropertyIfElse, AnIfElseCountsInEachPlace) {
  for (const char* place : kPropertyPlaces) {
    for (const PlacedProperty& property : kPlacedProperties) {
      ExpectPropertyCountsInPlace(place, property, kPlacedStimulus,
                                  kPlacedDeclarations);
    }
  }
}

TEST(PropertyIfElse, DISABLED_AnIfElseCountsInACompilationUnitProperty) {
  for (const PlacedProperty& property : kPlacedProperties) {
    ExpectPropertyCountsInPlace("unit", property, kPlacedStimulus,
                                kPlacedDeclarations);
  }
}

std::string ConditionSource(const std::string& condition) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic c, d, cx;\n"
         "  logic [1:0] v;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign c = tick inside {2};\n"
         "  assign d = tick inside {1};\n"
         "  assign v = tick == 2 ? 2'b10 : 2'b00;\n"
         "  assign cx = tick == 2 ? 1'bx : 1'b0;\n"
         "  p: assert property (@(posedge clk) if (" +
         condition +
         ") c else d) passes++; else fails++;\n"
         "  initial #40 $finish;\n"
         "endmodule\n";
}

TEST(PropertyIfElse, AVectorConditionIsTrueWhereItIsNonzero) {
  SimFixture f;
  auto* passes = RunAndFindVar(ConditionSource("v"), f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

TEST(PropertyIfElse, AnUnknownConditionTakesTheElseBranch) {
  SimFixture f;
  auto* passes = RunAndFindVar(ConditionSource("cx"), f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 3u);
}

}  // namespace
