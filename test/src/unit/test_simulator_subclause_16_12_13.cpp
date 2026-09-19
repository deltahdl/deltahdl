#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §16.12.13: a strong eventually (`s_eventually`) holds when the inner
// property_expr holds at some current or future clock tick within the range.
TEST(SvaEngineEventually, StrongHoldsWithWitness) {
  EXPECT_EQ(EvalEventually(/*strong=*/true, /*inner_holds_within_range=*/true,
                           /*all_range_ticks_present=*/true),
            PropertyResult::kPass);
}

// §16.12.13: a strong eventually fails when no current or future clock tick in
// the range satisfies the inner property_expr — even when the range's later
// ticks are not yet present, as for the unbounded `s_eventually [2:$]` form.
TEST(SvaEngineEventually, StrongFailsWithoutWitness) {
  EXPECT_EQ(EvalEventually(/*strong=*/true, /*inner_holds_within_range=*/false,
                           /*all_range_ticks_present=*/true),
            PropertyResult::kFail);
  EXPECT_EQ(EvalEventually(/*strong=*/true, /*inner_holds_within_range=*/false,
                           /*all_range_ticks_present=*/false),
            PropertyResult::kFail);
}

// §16.12.13: a weak `eventually` holds when the inner property_expr holds at
// some tick within the range, exactly as the strong form does.
TEST(SvaEngineEventually, WeakHoldsWithWitness) {
  EXPECT_EQ(EvalEventually(/*strong=*/false, /*inner_holds_within_range=*/true,
                           /*all_range_ticks_present=*/true),
            PropertyResult::kPass);
}

// §16.12.13: a weak eventually over a fully observed range fails when the inner
// property_expr held at none of the range's ticks.
TEST(SvaEngineEventually, WeakFailsWhenRangeFullyObservedWithoutWitness) {
  EXPECT_EQ(EvalEventually(/*strong=*/false, /*inner_holds_within_range=*/false,
                           /*all_range_ticks_present=*/true),
            PropertyResult::kFail);
}

// §16.12.13: a weak eventually also holds when not all clock ticks within the
// range exist, because the weak form does not require those later ticks to be
// present.
TEST(SvaEngineEventually, WeakHoldsWhenRangeTicksMissing) {
  EXPECT_EQ(EvalEventually(/*strong=*/false, /*inner_holds_within_range=*/false,
                           /*all_range_ticks_present=*/false),
            PropertyResult::kPass);
}

// §16.12.13: a weak eventually with a witness passes even when the range's
// later ticks are not all present — the satisfying tick is reached before any
// missing tick matters, so incomplete observation of the range does not change
// the pass.
TEST(SvaEngineEventually, WeakHoldsWithWitnessWhenRangeTicksMissing) {
  EXPECT_EQ(EvalEventually(/*strong=*/false, /*inner_holds_within_range=*/true,
                           /*all_range_ticks_present=*/false),
            PropertyResult::kPass);
}

// §16.12.13: the non-ranged `s_eventually` covers every current or future clock
// tick (equivalent to strong(##[*0:$] property_expr)), so a witness makes it
// pass even when later clock ticks are not all present.
TEST(SvaEngineEventually, NonRangedStrongTakesWitness) {
  EXPECT_EQ(EvalEventually(/*strong=*/true, /*inner_holds_within_range=*/true,
                           /*all_range_ticks_present=*/false),
            PropertyResult::kPass);
}

// --- Live cases: eventually properties over real source ---

// The module the cases share: clk rises at 5, 15, 25 and 35, tick n at
// 10n - 5, the tick counter counting through; a is high at tick 3 alone.
// `items` declare the assertions, counting in `passes` and `fails`.
std::string EventuallySource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic a;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign a = tick inside {3};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

// §16.12.13: `s_eventually a` is true if and only if a holds at some
// current or future tick: the attempts from 1, 2 and 3 are true at 3, and
// the attempt from 4, a never true again, fails when the run ends.
TEST(EventuallyProperty, StrongEventuallyNeedsAWitness) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      EventuallySource("  p: assert property (@(posedge clk) s_eventually a) "
                       "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 0u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

// §16.12.13: `eventually [0:1] a` is true where a holds at the attempt's
// tick or the next, or where not both exist: the attempt from 1 is false at
// 2, those from 2 and 3 true at 3, and the attempt from 4, its second tick
// never reached, true when the run ends.
TEST(EventuallyProperty, RangedWeakEventuallyHoldsWhereTheRangeIsCutShort) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      EventuallySource("  p: assert property (@(posedge clk) eventually [0:1] "
                       "a) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(passes->value.ToUint64(), 3u);
}

// §16.12.13: `s_eventually [0:1] a` needs a witness within the range, so
// the attempt from 4 fails when the run ends.
TEST(EventuallyProperty, RangedStrongEventuallyFailsWhereTheRangeIsCutShort) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      EventuallySource("  p: assert property (@(posedge clk) s_eventually "
                       "[0:1] a) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

// §16.12.13: `s_eventually [2:$] a`, the clause's p7, is true where a holds
// at some tick two or more after the attempt's: the attempt from 1 is true
// at 3, and those from 2, 3 and 4 fail when the run ends.
TEST(EventuallyProperty, UnboundedStrongRangeBeginsAfterItsMinimum) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      EventuallySource("  p: assert property (@(posedge clk) s_eventually "
                       "[2:$] a) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 0u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 3u);
}

}  // namespace
