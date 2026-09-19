#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §16.12.11: weak `always property_expr` holds when the inner property_expr
// held at every present clock tick and fails when it failed at one of them.
TEST(SvaEngine, WeakAlwaysTakesInnerVerdictOverPresentTicks) {
  EXPECT_EQ(EvalAlways(/*strong=*/false, /*all_covered_ticks_present=*/true,
                       /*inner_holds_at_present_ticks=*/true),
            PropertyResult::kPass);
  EXPECT_EQ(EvalAlways(/*strong=*/false, /*all_covered_ticks_present=*/true,
                       /*inner_holds_at_present_ticks=*/false),
            PropertyResult::kFail);
}

// §16.12.11: for a weak always it is not required that all clock ticks within
// the range exist, so missing covered ticks do not by themselves cause a
// failure.
TEST(SvaEngine, WeakAlwaysIgnoresMissingCoveredTicks) {
  EXPECT_EQ(EvalAlways(/*strong=*/false, /*all_covered_ticks_present=*/false,
                       /*inner_holds_at_present_ticks=*/true),
            PropertyResult::kPass);
}

// §16.12.11: strong `s_always` holds only when every covered tick exists and
// the inner property_expr held at each of them.
TEST(SvaEngine, StrongAlwaysRequiresPresentTicksAndInnerVerdict) {
  EXPECT_EQ(EvalAlways(/*strong=*/true, /*all_covered_ticks_present=*/true,
                       /*inner_holds_at_present_ticks=*/true),
            PropertyResult::kPass);
  EXPECT_EQ(EvalAlways(/*strong=*/true, /*all_covered_ticks_present=*/true,
                       /*inner_holds_at_present_ticks=*/false),
            PropertyResult::kFail);
}

// §16.12.11: strong always fails when a covered tick is missing — the dual of
// the weak form's pass in the same situation.
TEST(SvaEngine, StrongAlwaysFailsWhenCoveredTickMissing) {
  EXPECT_EQ(EvalAlways(/*strong=*/true, /*all_covered_ticks_present=*/false,
                       /*inner_holds_at_present_ticks=*/true),
            PropertyResult::kFail);
}

// §16.12.11: the non-ranged weak always covers every current or future tick,
// modelled as a minimum of 0 with an unbounded maximum, so every index from the
// current step onward is covered.
TEST(SvaEngine, NonRangedAlwaysCoversEveryFutureTick) {
  EXPECT_TRUE(
      AlwaysRangeCovers(/*index=*/0, /*range_min=*/0, kAlwaysUnboundedMax));
  EXPECT_TRUE(
      AlwaysRangeCovers(/*index=*/9, /*range_min=*/0, kAlwaysUnboundedMax));
}

// §16.12.11: a bounded range covers exactly the inclusive span of clock ticks
// it specifies; ticks before the minimum or after the maximum are not covered.
TEST(SvaEngine, BoundedRangeCoversInclusiveSpan) {
  EXPECT_FALSE(
      AlwaysRangeCovers(/*index=*/1, /*range_min=*/2, /*range_max=*/4));
  EXPECT_TRUE(AlwaysRangeCovers(/*index=*/2, /*range_min=*/2, /*range_max=*/4));
  EXPECT_TRUE(AlwaysRangeCovers(/*index=*/4, /*range_min=*/2, /*range_max=*/4));
  EXPECT_FALSE(
      AlwaysRangeCovers(/*index=*/5, /*range_min=*/2, /*range_max=*/4));
}

// §16.12.11: an unbounded weak range covers every tick from its minimum onward.
TEST(SvaEngine, UnboundedRangeCoversFromMinimumOnward) {
  EXPECT_FALSE(
      AlwaysRangeCovers(/*index=*/2, /*range_min=*/3, kAlwaysUnboundedMax));
  EXPECT_TRUE(
      AlwaysRangeCovers(/*index=*/3, /*range_min=*/3, kAlwaysUnboundedMax));
  EXPECT_TRUE(
      AlwaysRangeCovers(/*index=*/100, /*range_min=*/3, kAlwaysUnboundedMax));
}

// §16.12.11: for a strong always the covered ticks all exist when at least
// `range_max` further ticks are available, counting from the current step.
TEST(SvaEngine, StrongAlwaysTicksPresentWhenEnoughFutureTicks) {
  EXPECT_TRUE(
      AlwaysStrongTicksAllPresent(/*range_max=*/3, /*future_clock_ticks=*/3));
  EXPECT_TRUE(
      AlwaysStrongTicksAllPresent(/*range_max=*/3, /*future_clock_ticks=*/5));
  EXPECT_FALSE(
      AlwaysStrongTicksAllPresent(/*range_max=*/3, /*future_clock_ticks=*/2));
}

// §16.12.11: composing the helpers reproduces the strong-always semantics —
// when the range's ticks are not all present the property fails regardless of
// the inner verdict, and otherwise it takes the inner verdict.
TEST(SvaEngine, StrongAlwaysComposesPresenceWithInnerVerdict) {
  bool present =
      AlwaysStrongTicksAllPresent(/*range_max=*/4, /*future_clock_ticks=*/2);
  EXPECT_EQ(EvalAlways(/*strong=*/true, present,
                       /*inner_holds_at_present_ticks=*/true),
            PropertyResult::kFail);

  present =
      AlwaysStrongTicksAllPresent(/*range_max=*/4, /*future_clock_ticks=*/4);
  EXPECT_EQ(EvalAlways(/*strong=*/true, present,
                       /*inner_holds_at_present_ticks=*/true),
            PropertyResult::kPass);
}

// --- Live cases: always properties over real source ---

// The module the cases share: clk rises at 5, 15, 25 and 35, tick n at
// 10n - 5, the tick counter counting through; a is high at ticks 1 to 3 and
// b at every tick. `items` declare the assertions, counting in `passes` and
// `fails`.
std::string AlwaysSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic a, b;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign a = tick inside {1, 2, 3};\n"
         "  assign b = tick inside {1, 2, 3, 4};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

// §16.12.11: `always a` is true if and only if a holds at every current or
// future tick: every attempt fails at 4, where a is low, while `always b`,
// b high throughout, is decided by no tick and holds for every attempt when
// the run ends.
TEST(AlwaysProperty, WeakAlwaysHoldsUntilATickFails) {
  SimFixture f;
  auto* fails_at_four = RunAndFindVar(
      AlwaysSource("  p: assert property (@(posedge clk) always a) passes++; "
                   "else fails++;\n"),
      f, "passes");
  ASSERT_NE(fails_at_four, nullptr);
  EXPECT_EQ(fails_at_four->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 4u);
  SimFixture g;
  auto* holds = RunAndFindVar(
      AlwaysSource("  p: assert property (@(posedge clk) always b) passes++; "
                   "else fails++;\n"),
      g, "passes");
  ASSERT_NE(holds, nullptr);
  EXPECT_EQ(holds->value.ToUint64(), 0u);
  g.ctx.RunFinalBlocks();
  EXPECT_EQ(holds->value.ToUint64(), 4u);
  EXPECT_EQ(g.ctx.FindVariable("fails")->value.ToUint64(), 0u);
}

// §16.12.11: `always [0:1] b` needs b at the attempt's tick and the next
// where they exist, so the attempts from 1 to 3 are true at 2 to 4 and the
// attempt from 4, its second tick never reached, is true when the run
// ends.
TEST(AlwaysProperty, RangedWeakAlwaysNeedsOnlyTheTicksThatExist) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      AlwaysSource("  p: assert property (@(posedge clk) always [0:1] b) "
                   "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 0u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(passes->value.ToUint64(), 4u);
}

// §16.12.11: `s_always [0:1] b` needs every tick of the range to exist, so
// the attempt from 4 fails when the run ends.
TEST(AlwaysProperty, RangedStrongAlwaysNeedsEveryTickOfTheRange) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      AlwaysSource("  p: assert property (@(posedge clk) s_always [0:1] b) "
                   "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

// §16.12.11: the range begins after its minimum: `always [1:2] a` reads a
// at the next two ticks, so the attempt from 1 is true at 3 and those from
// 2 and 3 false at 4, where a is low, the attempt from 4 true at the end
// with no tick of its range reached.
TEST(AlwaysProperty, RangeBeginsAfterItsMinimum) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      AlwaysSource("  p: assert property (@(posedge clk) always [1:2] a) "
                   "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(passes->value.ToUint64(), 2u);
}

}  // namespace
