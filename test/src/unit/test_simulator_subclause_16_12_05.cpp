#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §16.12.5: a conjunction property holds if, and only if, both operand
// property expressions hold. Pass conjoined with pass yields pass.
TEST(PropertyConjunction, BothOperandsPass) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);
}

// A vacuous pass still counts as the operand holding, so conjoining it with
// a pass keeps the conjunction holding.
TEST(PropertyConjunction, VacuousOperandStillHolds) {
  EXPECT_EQ(
      EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kVacuousPass),
      PropertyResult::kPass);
}

// §16.12.5: if either operand fails the conjunction fails, regardless of
// which side carries the failure.
TEST(PropertyConjunction, LeftOperandFails) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kFail);
}

TEST(PropertyConjunction, RightOperandFails) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kFail);
}

// Edge case: when neither operand holds the conjunction still fails.
TEST(PropertyConjunction, BothOperandsFail) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kFail);
}

// Edge case: two vacuous passes both count as holding, so the conjunction
// holds vacuously rather than failing.
TEST(PropertyConjunction, BothOperandsVacuous) {
  EXPECT_EQ(EvalPropertyAnd(PropertyResult::kVacuousPass,
                            PropertyResult::kVacuousPass),
            PropertyResult::kPass);
}

// Edge case: a failure on one side dominates a vacuous hold on the other.
// The vacuous operand counts as holding, but the conjunction still needs both
// sides to hold, so the failing side forces an overall failure.
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

// A vacuous hold conjoined with a genuine pass still holds, mirroring the
// pass-with-vacuous case from the other operand order.
TEST(PropertyConjunction, VacuousWithPassHolds) {
  EXPECT_EQ(
      EvalPropertyAnd(PropertyResult::kVacuousPass, PropertyResult::kPass),
      PropertyResult::kPass);
}

// --- Live cases: conjunction properties over real source ---

// The module the cases share: clk rises at 5, 15, 25 and 35, tick n at
// 10n - 5, the tick counter counting through; a is high at ticks 1 and 4, b
// at 1 and 2, c at 2 and 3 and d at 1 and 4, so a ##1 c matches from 1 at
// 2, cannot match from 2 or 3, and is unfinished from 4 when the run ends.
// `items` declare the assertions, counting in `passes` and `fails`.
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

// §16.12.5: `a and b` is true at an attempt if and only if both operands
// are: true at 1 alone.
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

// §16.12.5: a sequence operand beside a boolean: `(a ##1 c) and d` is false
// as soon as either operand is and true once both are: the attempt from 1 is
// true at 2, where its sequence matches, the attempts from 2 and 3 are false
// where their sequence cannot match, and the attempt from 4, d true and its
// weak sequence unfinished at the end of the run, is true then.
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

// §16.12.5 with §16.12.2: `strong(a ##1 c) and d` reads the sequence
// unfinished at the end of the run as false, so the attempt from 4 fails
// then; and a boolean operand false at the attempt's tick decides the
// conjunction false at once, the sequence's attempt notwithstanding.
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

// Table 16-3: `and` binds tighter than `or`, so `a or b and c` is a or (b
// and c): true at 1, 2 and 4 and false at 3, where (a or b) and c would be
// true at 2 alone.
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

}  // namespace
