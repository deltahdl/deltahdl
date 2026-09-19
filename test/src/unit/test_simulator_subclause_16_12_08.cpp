#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_queues.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

struct SvaFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

namespace {

TEST(SvaEngine, PropertyNot) {
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kPass), PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kFail), PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kVacuousPass),
            PropertyResult::kFail);
}

// §16.12.8: `property_expr1 implies property_expr2` holds if, and only if, the
// antecedent fails to hold or the consequent holds. The antecedent holding with
// a holding consequent passes; a holding antecedent with a failing consequent
// fails; a failing antecedent holds vacuously regardless of the consequent.
TEST(SvaEngine, PropertyImplies) {
  EXPECT_EQ(EvalPropertyImplies(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyImplies(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyImplies(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyImplies(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kPass);
}

// §16.12.8: `property_expr1 iff property_expr2` holds if, and only if, the two
// operands' verdicts agree — both hold or both fail to hold; disagreement
// fails in either direction.
TEST(SvaEngine, PropertyIff) {
  EXPECT_EQ(EvalPropertyIff(PropertyResult::kPass, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyIff(PropertyResult::kFail, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyIff(PropertyResult::kPass, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyIff(PropertyResult::kFail, PropertyResult::kPass),
            PropertyResult::kFail);
}

// §16.12.8: a vacuous pass counts as the operand holding, so it behaves like an
// ordinary pass on either side of implies and iff. The implies consequent is a
// distinct, asymmetric operand: a consequent that holds vacuously (as an inner
// vacuously passing property_expr does) still makes the implication hold, both
// when the antecedent holds and when it fails to hold.
TEST(SvaEngine, ImpliesIffTreatVacuousPassAsHolding) {
  EXPECT_EQ(
      EvalPropertyImplies(PropertyResult::kVacuousPass, PropertyResult::kFail),
      PropertyResult::kFail);
  EXPECT_EQ(
      EvalPropertyImplies(PropertyResult::kPass, PropertyResult::kVacuousPass),
      PropertyResult::kPass);
  EXPECT_EQ(
      EvalPropertyImplies(PropertyResult::kFail, PropertyResult::kVacuousPass),
      PropertyResult::kPass);
  EXPECT_EQ(
      EvalPropertyIff(PropertyResult::kVacuousPass, PropertyResult::kPass),
      PropertyResult::kPass);
  EXPECT_EQ(
      EvalPropertyIff(PropertyResult::kVacuousPass, PropertyResult::kFail),
      PropertyResult::kFail);
}

// --- Live cases: implies and iff over real source ---

// The module the cases share: clk rises at 5, 15, 25 and 35, tick n at
// 10n - 5, the tick counter counting through; a is high at ticks 1 and 3, b
// at 2 and 3 and c at 2 and 3. `items` declare the assertions, counting in
// `passes` and `fails`.
std::string ImpliesSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic a, b, c;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign a = tick inside {1, 3};\n"
         "  assign b = tick inside {2, 3};\n"
         "  assign c = tick inside {2, 3};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

// §16.12.8: `a implies b` is true if and only if a is false or b true:
// false at 1 alone.
TEST(ImpliesIffProperty, ImpliesHoldsWhereTheFirstIsFalseOrTheSecondTrue) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ImpliesSource("  p: assert property (@(posedge clk) a implies b) "
                    "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

// §16.12.8: `a iff b` is true if and only if both are false or both true:
// true at 3 and 4, false at 1 and 2.
TEST(ImpliesIffProperty, IffHoldsWhereBothAreAlike) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ImpliesSource("  p: assert property (@(posedge clk) a iff b) passes++; "
                    "else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

// Table 16-3: `iff` binds tighter than `implies`, so `a iff b implies c` is
// (a iff b) implies c: false at 4 alone, where a iff b holds with c low;
// a iff (b implies c) would be false at 2 and 4.
TEST(ImpliesIffProperty, IffBindsTighterThanImplies) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ImpliesSource("  p: assert property (@(posedge clk) a iff b implies c) "
                    "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

// §16.12.8: an operand may be a sequence: `(a ##1 b) implies c` is false
// at 2 for the attempt from 1, whose sequence matches there with c low at 1,
// true at 2 for the attempt from 2, whose sequence cannot match, true at 3
// for the attempt from 3 through c, its sequence still in flight, and true
// at 4 for the attempt from 4.
TEST(ImpliesIffProperty, ASequenceOperandIsDecidedWhereItMatchesOrCannot) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ImpliesSource("  p: assert property (@(posedge clk) (a ##1 b) implies "
                    "c) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

}  // namespace
