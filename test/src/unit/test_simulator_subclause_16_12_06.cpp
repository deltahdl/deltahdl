#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
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

}  // namespace
