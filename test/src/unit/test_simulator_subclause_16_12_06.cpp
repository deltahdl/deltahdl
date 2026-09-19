#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §16.12.6: in the single-branch form `if (cond) p`, when the guard holds the
// property result is exactly that of the then-branch.
TEST(PropertyIfElse, SingleBranchGuardTrueTakesThen) {
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/true, PropertyResult::kPass,
                               /*has_else=*/false, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/true, PropertyResult::kFail,
                               /*has_else=*/false, PropertyResult::kPass),
            PropertyResult::kFail);
}

// §16.12.6: the first form is true if the guard is false, regardless of the
// then-branch. With no else there is nothing to check, so it holds vacuously.
TEST(PropertyIfElse, SingleBranchGuardFalseHoldsVacuously) {
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/false, PropertyResult::kFail,
                               /*has_else=*/false, PropertyResult::kPass),
            PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/false, PropertyResult::kPass,
                               /*has_else=*/false, PropertyResult::kPass),
            PropertyResult::kVacuousPass);
}

// §16.12.6: in the two-branch form `if (cond) p1 else p2`, a true guard makes
// the result that of property_expr1.
TEST(PropertyIfElse, TwoBranchGuardTrueTakesThen) {
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/true, PropertyResult::kPass,
                               /*has_else=*/true, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/true, PropertyResult::kFail,
                               /*has_else=*/true, PropertyResult::kPass),
            PropertyResult::kFail);
}

// §16.12.6: in the two-branch form a false guard routes evaluation to the
// else-branch, so the result is that of property_expr2.
TEST(PropertyIfElse, TwoBranchGuardFalseTakesElse) {
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/false, PropertyResult::kFail,
                               /*has_else=*/true, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/false, PropertyResult::kPass,
                               /*has_else=*/true, PropertyResult::kFail),
            PropertyResult::kFail);
}

// §16.12.6 edge case: the result is exactly the selected branch's result, so a
// vacuous hold in the chosen branch is carried through unchanged rather than
// being normalized to a plain pass.
TEST(PropertyIfElse, SelectedBranchVacuousResultPropagates) {
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/true, PropertyResult::kVacuousPass,
                               /*has_else=*/true, PropertyResult::kFail),
            PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/false, PropertyResult::kFail,
                               /*has_else=*/true, PropertyResult::kVacuousPass),
            PropertyResult::kVacuousPass);
}

// §16.12.6 edge case: an as-yet unresolved (pending) result in the chosen
// branch is likewise carried through, since the if-else result tracks the
// selected branch and defers along with it.
TEST(PropertyIfElse, SelectedBranchPendingResultPropagates) {
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/true, PropertyResult::kPending,
                               /*has_else=*/true, PropertyResult::kPass),
            PropertyResult::kPending);
  EXPECT_EQ(EvalPropertyIfElse(/*cond=*/false, PropertyResult::kPass,
                               /*has_else=*/true, PropertyResult::kPending),
            PropertyResult::kPending);
}

// --- Live cases: if-else properties over real source ---

// The module the cases share: clk rises at 5, 15, 25 and 35, tick n at
// 10n - 5, the tick counter counting through; req is high at ticks 1, 2 and
// 4, gnt at 1 and 4, done at 2 and idle at 1, so gnt ##1 done matches from
// 1 at 2, cannot match from 2, and is unfinished from 4 when the run ends.
// `items` declare the assertions, counting in `passes` and `fails`.
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

// §16.12.6: `if (req) gnt` is true where req is false or gnt true: false at
// 2 alone.
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

// §16.12.6: `if (req) gnt else idle` is true where req is true with gnt or
// false with idle: false at 2, gnt low, and at 3, idle low.
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

// §16.12.6: a branch may be a sequence: `if (req) gnt ##1 done else idle`
// is true at 2 for the attempt from 1, whose sequence matches there, false
// at 2 for the attempt from 2, whose sequence cannot match, false at 3
// through idle, and, its weak sequence unfinished at the end of the run,
// true then for the attempt from 4.
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

// Table 16-3 puts if-else below every other operator, so `if (req) gnt and
// idle` is if (req) (gnt and idle): true at 1 and, req false, at 3, and
// false at 2 and 4; (if (req) gnt) and idle would be true at 1 alone.
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
