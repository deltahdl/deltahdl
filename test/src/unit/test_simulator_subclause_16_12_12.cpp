#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sva_engine.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Tests for LRM §16.12.12 "Until property", covering the four forms:
//   a until        b  (weak,   non-overlapping)
//   a s_until      b  (strong, non-overlapping)
//   a until_with   b  (weak,   overlapping)
//   a s_until_with b  (strong, overlapping)
//
// `UntilLeftHoldsRequired` models where the left operand must hold relative to
// the first tick at which the right operand holds (the overlapping vs
// non-overlapping axis); `EvalUntil` combines that with whether the right
// operand ever holds (the weak vs strong axis).

// §16.12.12: for the non-overlapping forms the left operand is required only on
// the ticks before the first tick where the right operand holds, so it need not
// hold at that tick itself.
TEST(SvaEngineUntil, NonOverlappingExcludesRhsTick) {
  // Right operand first holds at offset 2; left operand held at ticks 0 and 1.
  EXPECT_TRUE(
      UntilLeftHoldsRequired(/*overlapping=*/false, /*lhs_run_length=*/2,
                             /*first_rhs_index=*/2, /*trace_length=*/5));
  // Left operand stopped holding before the required window was covered.
  EXPECT_FALSE(
      UntilLeftHoldsRequired(/*overlapping=*/false, /*lhs_run_length=*/1,
                             /*first_rhs_index=*/2, /*trace_length=*/5));
}

// §16.12.12: for the overlapping forms the left operand is also required at the
// tick where the right operand first holds.
TEST(SvaEngineUntil, OverlappingIncludesRhsTick) {
  // The same trace that satisfies the non-overlapping form fails here because
  // the left operand must also hold at the right operand's tick (offset 2).
  EXPECT_FALSE(
      UntilLeftHoldsRequired(/*overlapping=*/true, /*lhs_run_length=*/2,
                             /*first_rhs_index=*/2, /*trace_length=*/5));
  EXPECT_TRUE(UntilLeftHoldsRequired(/*overlapping=*/true, /*lhs_run_length=*/3,
                                     /*first_rhs_index=*/2,
                                     /*trace_length=*/5));
}

// §16.12.12: when the right operand holds at the starting tick, the
// non-overlapping form does not require the left operand to hold there at all.
TEST(SvaEngineUntil, NonOverlappingRhsAtStartRequiresNothing) {
  EXPECT_TRUE(
      UntilLeftHoldsRequired(/*overlapping=*/false, /*lhs_run_length=*/0,
                             /*first_rhs_index=*/0, /*trace_length=*/4));
}

// §16.12.12: when the right operand holds at the starting tick, the overlapping
// form still requires the left operand to hold at that one (overlapping) tick.
TEST(SvaEngineUntil, OverlappingRhsAtStartRequiresLhsThere) {
  EXPECT_FALSE(
      UntilLeftHoldsRequired(/*overlapping=*/true, /*lhs_run_length=*/0,
                             /*first_rhs_index=*/0, /*trace_length=*/4));
  EXPECT_TRUE(UntilLeftHoldsRequired(/*overlapping=*/true, /*lhs_run_length=*/1,
                                     /*first_rhs_index=*/0,
                                     /*trace_length=*/4));
}

// §16.12.12: when the right operand never holds, the left operand is required
// at every tick of the trace for both windowings.
TEST(SvaEngineUntil, RhsNeverRequiresLhsEverywhere) {
  EXPECT_TRUE(UntilLeftHoldsRequired(/*overlapping=*/false,
                                     /*lhs_run_length=*/3, kUntilRhsNever,
                                     /*trace_length=*/3));
  EXPECT_TRUE(UntilLeftHoldsRequired(/*overlapping=*/true, /*lhs_run_length=*/3,
                                     kUntilRhsNever, /*trace_length=*/3));
  EXPECT_FALSE(UntilLeftHoldsRequired(/*overlapping=*/false,
                                      /*lhs_run_length=*/2, kUntilRhsNever,
                                      /*trace_length=*/3));
}

// §16.12.12: a weak until holds whenever the left operand held over its
// required window, regardless of whether the right operand ever holds.
TEST(SvaEngineUntil, WeakHoldsRegardlessOfRhsPresence) {
  EXPECT_EQ(EvalUntil(/*strong=*/false, /*rhs_holds_eventually=*/false,
                      /*lhs_holds_required=*/true),
            PropertyResult::kPass);
  EXPECT_EQ(EvalUntil(/*strong=*/false, /*rhs_holds_eventually=*/true,
                      /*lhs_holds_required=*/true),
            PropertyResult::kPass);
}

// §16.12.12: any until form fails when the left operand did not hold across its
// required window.
TEST(SvaEngineUntil, FailsWhenLeftOperandDidNotHold) {
  EXPECT_EQ(EvalUntil(/*strong=*/false, /*rhs_holds_eventually=*/true,
                      /*lhs_holds_required=*/false),
            PropertyResult::kFail);
  EXPECT_EQ(EvalUntil(/*strong=*/true, /*rhs_holds_eventually=*/true,
                      /*lhs_holds_required=*/false),
            PropertyResult::kFail);
}

// §16.12.12: a strong until requires a current or future tick at which the
// right operand holds; if none exists the property fails even though the same
// trace satisfies the corresponding weak form.
TEST(SvaEngineUntil, StrongRequiresRhsToHold) {
  EXPECT_EQ(EvalUntil(/*strong=*/true, /*rhs_holds_eventually=*/false,
                      /*lhs_holds_required=*/true),
            PropertyResult::kFail);
  EXPECT_EQ(EvalUntil(/*strong=*/true, /*rhs_holds_eventually=*/true,
                      /*lhs_holds_required=*/true),
            PropertyResult::kPass);
}

// §16.12.12: composing the helpers reproduces `a until b` (p1) — the left
// operand holds up to the first right-operand tick and the weak form holds even
// when the right operand only holds later.
TEST(SvaEngineUntil, ComposesWeakNonOverlapping) {
  bool lhs = UntilLeftHoldsRequired(/*overlapping=*/false, /*lhs_run_length=*/2,
                                    /*first_rhs_index=*/2, /*trace_length=*/5);
  EXPECT_EQ(EvalUntil(/*strong=*/false, /*rhs_holds_eventually=*/true, lhs),
            PropertyResult::kPass);
}

// §16.12.12: composing the helpers reproduces `a s_until b` (p2) failing when
// the right operand never holds, even though the left operand holds everywhere.
TEST(SvaEngineUntil, ComposesStrongNonOverlappingFailsWithoutRhs) {
  bool lhs = UntilLeftHoldsRequired(/*overlapping=*/false, /*lhs_run_length=*/3,
                                    kUntilRhsNever, /*trace_length=*/3);
  EXPECT_EQ(EvalUntil(/*strong=*/true, /*rhs_holds_eventually=*/false, lhs),
            PropertyResult::kFail);
}

// §16.12.12: composing the helpers reproduces `a s_until_with b` (p4) — the
// left operand holds through and including the right-operand tick and the right
// operand holds, so the strong overlapping form passes.
TEST(SvaEngineUntil, ComposesStrongOverlapping) {
  bool lhs = UntilLeftHoldsRequired(/*overlapping=*/true, /*lhs_run_length=*/3,
                                    /*first_rhs_index=*/2, /*trace_length=*/5);
  EXPECT_EQ(EvalUntil(/*strong=*/true, /*rhs_holds_eventually=*/true, lhs),
            PropertyResult::kPass);
}

// §16.12.12: composing the helpers reproduces `a until_with b` (p3) — the weak
// overlapping form requires the left operand through and including the
// right-operand tick but, being weak, does not require the right operand to
// hold at all. Here the left operand holds at every tick while the right
// operand never holds, so the property still passes.
TEST(SvaEngineUntil, ComposesWeakOverlapping) {
  bool lhs = UntilLeftHoldsRequired(/*overlapping=*/true, /*lhs_run_length=*/3,
                                    kUntilRhsNever, /*trace_length=*/3);
  EXPECT_EQ(EvalUntil(/*strong=*/false, /*rhs_holds_eventually=*/false, lhs),
            PropertyResult::kPass);
}

// §16.12.12: the weak overlapping form still enforces the left operand at the
// overlapping (right-operand) tick — when the left operand drops out exactly at
// that tick the property fails even though the right operand holds there.
TEST(SvaEngineUntil, ComposesWeakOverlappingFailsAtRhsTick) {
  bool lhs = UntilLeftHoldsRequired(/*overlapping=*/true, /*lhs_run_length=*/2,
                                    /*first_rhs_index=*/2, /*trace_length=*/5);
  EXPECT_EQ(EvalUntil(/*strong=*/false, /*rhs_holds_eventually=*/true, lhs),
            PropertyResult::kFail);
}

// --- Live cases: until properties over real source ---

// The module the cases share: clk rises at 5, 15, 25 and 35, tick n at
// 10n - 5, the tick counter counting through; a is high at ticks 1, 2 and 4,
// b at 3 and c at every tick. `items` declare the assertions, counting in
// `passes` and `fails`.
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

// §16.12.12: `a until b` is true where a holds at every tick from the
// attempt's until, not including, a tick b holds at: the attempts from 1, 2
// and 3 are true at 3, a not needed there, and the attempt from 4, a high
// with b never true again, is true when the run ends; `a s_until b` needs
// a tick b holds at and fails then instead.
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

// §16.12.12: `a until_with b` needs a at the tick b holds at as well, so
// with a low at 3 the attempts from 1, 2 and 3 fail there, and the attempt
// from 4 is true when the run ends; `c until_with b`, c high throughout, is
// true at 3 for those attempts.
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

// §16.12.12: `c s_until_with b` needs a tick b holds at, so the attempt
// from 4 fails when the run ends where `c until_with b` holds.
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

// §16.12.12: `b until a` is decided true at the first tick a holds at, b
// not needed there, so the attempts from 1, 2 and 4 are true at their own
// tick, a high, and the attempt from 3 passes its tick, b high with a low,
// and is true at 4. `b until_with a` needs b where a holds, so the attempts
// from 1, 2 and 4 fail at their own tick, b low, and the attempt from 3 at
// 4.
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
