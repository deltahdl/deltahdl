#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SvaEngineUntil, NonOverlappingExcludesRhsTick) {
  EXPECT_TRUE(UntilLeftHoldsRequired(false, 2, 2, 5));
  EXPECT_FALSE(UntilLeftHoldsRequired(false, 1, 2, 5));
}

TEST(SvaEngineUntil, OverlappingIncludesRhsTick) {
  EXPECT_FALSE(UntilLeftHoldsRequired(true, 2, 2, 5));
  EXPECT_TRUE(UntilLeftHoldsRequired(true, 3, 2, 5));
}

TEST(SvaEngineUntil, NonOverlappingRhsAtStartRequiresNothing) {
  EXPECT_TRUE(UntilLeftHoldsRequired(false, 0, 0, 4));
}

TEST(SvaEngineUntil, OverlappingRhsAtStartRequiresLhsThere) {
  EXPECT_FALSE(UntilLeftHoldsRequired(true, 0, 0, 4));
  EXPECT_TRUE(UntilLeftHoldsRequired(true, 1, 0, 4));
}

TEST(SvaEngineUntil, RhsNeverRequiresLhsEverywhere) {
  EXPECT_TRUE(UntilLeftHoldsRequired(false, 3, kUntilRhsNever, 3));
  EXPECT_TRUE(UntilLeftHoldsRequired(true, 3, kUntilRhsNever, 3));
  EXPECT_FALSE(UntilLeftHoldsRequired(false, 2, kUntilRhsNever, 3));
}

TEST(SvaEngineUntil, WeakHoldsRegardlessOfRhsPresence) {
  EXPECT_EQ(EvalUntil(false, false, true), PropertyResult::kPass);
  EXPECT_EQ(EvalUntil(false, true, true), PropertyResult::kPass);
}

TEST(SvaEngineUntil, FailsWhenLeftOperandDidNotHold) {
  EXPECT_EQ(EvalUntil(false, true, false), PropertyResult::kFail);
  EXPECT_EQ(EvalUntil(true, true, false), PropertyResult::kFail);
}

TEST(SvaEngineUntil, StrongRequiresRhsToHold) {
  EXPECT_EQ(EvalUntil(true, false, true), PropertyResult::kFail);
  EXPECT_EQ(EvalUntil(true, true, true), PropertyResult::kPass);
}

TEST(SvaEngineUntil, ComposesWeakNonOverlapping) {
  bool lhs = UntilLeftHoldsRequired(false, 2, 2, 5);
  EXPECT_EQ(EvalUntil(false, true, lhs), PropertyResult::kPass);
}

TEST(SvaEngineUntil, ComposesStrongNonOverlappingFailsWithoutRhs) {
  bool lhs = UntilLeftHoldsRequired(false, 3, kUntilRhsNever, 3);
  EXPECT_EQ(EvalUntil(true, false, lhs), PropertyResult::kFail);
}

TEST(SvaEngineUntil, ComposesStrongOverlapping) {
  bool lhs = UntilLeftHoldsRequired(true, 3, 2, 5);
  EXPECT_EQ(EvalUntil(true, true, lhs), PropertyResult::kPass);
}

TEST(SvaEngineUntil, ComposesWeakOverlapping) {
  bool lhs = UntilLeftHoldsRequired(true, 3, kUntilRhsNever, 3);
  EXPECT_EQ(EvalUntil(false, false, lhs), PropertyResult::kPass);
}

TEST(SvaEngineUntil, ComposesWeakOverlappingFailsAtRhsTick) {
  bool lhs = UntilLeftHoldsRequired(true, 2, 2, 5);
  EXPECT_EQ(EvalUntil(false, true, lhs), PropertyResult::kFail);
}

std::string UntilSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic a, b, c;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign a = tick inside {1, 2, 4};\n"
         "  assign b = tick inside {3};\n"
         "  assign c = tick inside {1, 2, 3, 4};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

TEST(UntilProperty, NonOverlappingFormsExcludeTheTickTheSecondHoldsAt) {
  SimFixture f;
  auto* weak = RunAndFindVar(
      UntilSource("  p: assert property (@(posedge clk) a until b) passes++; "
                  "else fails++;\n"),
      f, "passes");
  ASSERT_NE(weak, nullptr);
  EXPECT_EQ(weak->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 0u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(weak->value.ToUint64(), 4u);
  SimFixture g;
  auto* strong = RunAndFindVar(
      UntilSource("  p: assert property (@(posedge clk) a s_until b) "
                  "passes++; else fails++;\n"),
      g, "passes");
  ASSERT_NE(strong, nullptr);
  EXPECT_EQ(strong->value.ToUint64(), 3u);
  g.ctx.RunFinalBlocks();
  EXPECT_EQ(g.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

TEST(UntilProperty, OverlappingFormsIncludeTheTickTheSecondHoldsAt) {
  SimFixture f;
  auto* a_fails = RunAndFindVar(
      UntilSource("  p: assert property (@(posedge clk) a until_with b) "
                  "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(a_fails, nullptr);
  EXPECT_EQ(a_fails->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 3u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(a_fails->value.ToUint64(), 1u);
  SimFixture g;
  auto* c_holds = RunAndFindVar(
      UntilSource("  p: assert property (@(posedge clk) c until_with b) "
                  "passes++; else fails++;\n"),
      g, "passes");
  ASSERT_NE(c_holds, nullptr);
  EXPECT_EQ(c_holds->value.ToUint64(), 3u);
  EXPECT_EQ(g.ctx.FindVariable("fails")->value.ToUint64(), 0u);
}

TEST(UntilProperty, StrongOverlappingFormNeedsTheSecondToHold) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      UntilSource("  p: assert property (@(posedge clk) c s_until_with b) "
                  "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

TEST(UntilProperty, TheFirstOperandFailingBeforeTheSecondHoldsFails) {
  SimFixture f;
  auto* decided_by_a = RunAndFindVar(
      UntilSource("  p: assert property (@(posedge clk) b until a) passes++; "
                  "else fails++;\n"),
      f, "passes");
  ASSERT_NE(decided_by_a, nullptr);
  EXPECT_EQ(decided_by_a->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 0u);
  SimFixture g;
  auto* needs_b = RunAndFindVar(
      UntilSource("  p: assert property (@(posedge clk) b until_with a) "
                  "passes++; else fails++;\n"),
      g, "passes");
  ASSERT_NE(needs_b, nullptr);
  EXPECT_EQ(needs_b->value.ToUint64(), 0u);
  EXPECT_EQ(g.ctx.FindVariable("fails")->value.ToUint64(), 4u);
}

}  // namespace
