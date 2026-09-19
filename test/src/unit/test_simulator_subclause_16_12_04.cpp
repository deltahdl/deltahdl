#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §16.12.4: a disjunction property holds if, and only if, at least one of its
// two operand property expressions holds. Two passing operands plainly hold.
TEST(PropertyDisjunction, BothOperandsPass) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);
}

// §16.12.4: one holding operand is enough, so a passing left operand carries
// the disjunction even when the right operand fails.
TEST(PropertyDisjunction, LeftOperandPasses) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kPass);
}

// §16.12.4: symmetric to the previous case — a passing right operand alone
// makes the disjunction hold.
TEST(PropertyDisjunction, RightOperandPasses) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kPass);
}

// §16.12.4: only when neither operand holds does the disjunction fail.
TEST(PropertyDisjunction, BothOperandsFail) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kFail);
}

// A vacuous pass counts as the operand holding, so it satisfies the
// "at least one holds" condition on its own.
TEST(PropertyDisjunction, VacuousLeftStillHolds) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kVacuousPass, PropertyResult::kFail),
            PropertyResult::kPass);
}

TEST(PropertyDisjunction, VacuousRightStillHolds) {
  EXPECT_EQ(EvalPropertyOr(PropertyResult::kFail, PropertyResult::kVacuousPass),
            PropertyResult::kPass);
}

// --- Live cases: disjunction properties over real source ---

// The module the cases share: clk rises at 5, 15, 25 and 35, tick n at
// 10n - 5, the tick counter counting through; a is high at ticks 1 and 4,
// b at 2 and c at 3, so a ##1 b matches from 1 at 2, cannot match from 2 or
// 3, and is unfinished from 4 when the run ends. `items` declare the
// assertions, counting in `passes` and `fails`.
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

// §16.12.4: `a or b` is true at an attempt if and only if at least one
// operand is: true at 1, 2 and 4 and false at 3.
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

// §16.12.4: a sequence operand beside a boolean: `(a ##1 b) or c` is
// decided where either operand is: the attempt from 1 is true at 2, where
// its sequence matches, the attempt from 2 is false there, both operands
// false, the attempt from 3 is true through c, and the attempt from 4,
// its weak sequence unfinished at the end of the run, is true then.
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

// §16.12.4 with §16.12.2: `strong(a ##1 b) or c` reads the sequence
// unfinished at the end of the run as false, so the attempt from 4 is false
// then.
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

// §16.12.4 with Table 16-3: `not` binds tighter than `or`, so `not a or b`
// is (not a) or b: false at 1 and 4, where a is high and b low, and true
// at 2 and 3.
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

}  // namespace
