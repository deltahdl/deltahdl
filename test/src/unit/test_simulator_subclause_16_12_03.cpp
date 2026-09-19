#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sampling.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §16.12.3: `not property_expr` returns the opposite of the underlying
// property_expr. A true underlying evaluation makes the negation false.
TEST(NegationProperty, NotOfTrueIsFalse) {
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kPass), PropertyResult::kFail);
}

// §16.12.3: a false underlying evaluation makes the negation true.
TEST(NegationProperty, NotOfFalseIsTrue) {
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kFail), PropertyResult::kPass);
}

// §16.12.3: the negation is the complement of the underlying verdict, and each
// attempt of the negation drives exactly one attempt of property_expr — so the
// result is a total function of that single underlying verdict. A vacuous pass
// counts as the property holding, so its negation fails.
TEST(NegationProperty, ComplementOfEveryUnderlyingVerdict) {
  EXPECT_EQ(EvalPropertyNot(EvalPropertyNot(PropertyResult::kPass)),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyNot(EvalPropertyNot(PropertyResult::kFail)),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kVacuousPass),
            PropertyResult::kFail);
}

// §16.12.3: the `not` operator switches the strength of the property it
// negates — a weak property becomes strong.
TEST(NegationProperty, NegationMakesWeakStrong) {
  EXPECT_EQ(NegatePropertyStrength(SequencePropertyStrength::kWeak),
            SequencePropertyStrength::kStrong);
}

// §16.12.3: negating a strong property yields a weak one. This is why the LRM
// recommends `not strong(a ##1 b)` over a bare `not a ##1 b` in an assertion:
// the bare sequence is weak, so its negation stays weak.
TEST(NegationProperty, NegationMakesStrongWeak) {
  EXPECT_EQ(NegatePropertyStrength(SequencePropertyStrength::kStrong),
            SequencePropertyStrength::kWeak);
}

// --- Live cases: negation properties over real source ---

// The module the cases share: clk rises at 5, 15, 25 and 35, tick n at
// 10n - 5, the tick counter counting through; a is high at ticks 1, 2 and 4
// and b at 2, so a ##1 b matches from 1, the attempts from 2 and 3 fail at 3
// and the one from 4 is unfinished when the run ends; busy is high at 3.
// `items` declare the assertions, counting in `passes` and `fails`.
std::string NegationSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic a, b, busy;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign a = tick inside {1, 2, 4};\n"
         "  assign b = tick inside {2};\n"
         "  assign busy = tick inside {3};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

// §16.12.3: `not busy` evaluates to the opposite of busy at each attempt,
// three passes and one failure, and the same through a named property whose
// body is the negation.
TEST(NegationProperty, NotOfABooleanIsItsOpposite) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      NegationSource("  a1: assert property (@(posedge clk) not busy) "
                     "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  SimFixture g;
  auto* named = RunAndFindVar(
      NegationSource(
          "  property p_idle;\n"
          "    @(posedge clk) not busy;\n"
          "  endproperty\n"
          "  a2: assert property (p_idle) passes++; else fails++;\n"),
      g, "passes");
  ASSERT_NE(named, nullptr);
  EXPECT_EQ(named->value.ToUint64(), 3u);
  EXPECT_EQ(g.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

// §16.12.3: the clause's a1, `not a ##1 b`, negates the weak sequence: the
// attempt from 1, whose sequence matches at 2, fails there, the attempts
// from 2 and 3, whose sequence cannot match by 3, pass there, and the attempt
// from 4, whose weak sequence holds unfinished at the end, fails when the run
// ends: two passes and, once the final blocks have run, two failures.
TEST(NegationProperty, NotOfAWeakSequenceFailsUnfinishedAtTheEnd) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      NegationSource("  a1: assert property (@(posedge clk) not a ##1 b) "
                     "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

// §16.12.3: the clause's a2, `not strong(a ##1 b)`, switches the strength
// the other way, so the attempt from 4, whose strong sequence has no match
// by the end, passes rather than failing then: two passes and one failure,
// the final blocks adding nothing.
TEST(NegationProperty, NotOfAStrongSequenceHoldsUnfinishedAtTheEnd) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      NegationSource("  a2: assert property (@(posedge clk) not strong(a ##1 "
                     "b)) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

// §16.12.3: `not not busy` is busy.
TEST(NegationProperty, TwoNegationsCancel) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      NegationSource("  a1: assert property (@(posedge clk) not not busy) "
                     "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 3u);
}

}  // namespace
