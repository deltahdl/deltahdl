#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §16.12: the result of property evaluation is either true or false. When
// an implication evaluation completes, EvalImplication returns one of the
// boolean outcomes (kPass / kFail) — never the not-yet-determined kPending.
TEST(PropertyEvaluation, PropertyEvaluationResultIsBoolean) {
  auto pass = EvalImplication(true, true, false);
  auto fail = EvalImplication(true, false, false);
  EXPECT_EQ(pass, PropertyResult::kPass);
  EXPECT_EQ(fail, PropertyResult::kFail);
  EXPECT_NE(pass, PropertyResult::kPending);
  EXPECT_NE(fail, PropertyResult::kPending);
}

// §16.12: a vacuous outcome still resolves to true; the rule is that an
// evaluation that completes yields a boolean.
TEST(PropertyEvaluation, VacuousResolvesToTrue) {
  auto v = EvalImplication(false, false, false);
  EXPECT_EQ(v, PropertyResult::kVacuousPass);
}

// §16.12: a disable iff that fires preempts evaluation; per the LRM this
// resolves as not-failed (modeled here as a vacuous pass), matching the
// "true or false" boundary at evaluation end.
TEST(PropertyEvaluation, DisableIffPreemptsToVacuousPass) {
  auto inner = EvalImplication(true, false, false);
  EXPECT_EQ(inner, PropertyResult::kFail);
  auto preempted = EvalWithDisableIff(true, inner);
  EXPECT_EQ(preempted, PropertyResult::kVacuousPass);
}

// --- Live cases: concurrent assertions over real source ---

// The module the cases share: clk rises at 5, 15, 25 and 35, tick n at
// 10n - 5, the tick counter counting through; sig is high at ticks 2 and 3
// and rst at 2 and 4; and the assertion `items` declare count their passes
// and failures in `passes` and `fails`.
std::string PropertySource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic sig, rst;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign sig = tick inside {2, 3};\n"
         "  assign rst = tick inside {2, 4};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

const char* const kCounting = " passes++; else fails++;\n";

// §16.12: an attempt at which the disable condition is true is disabled,
// neither succeeding nor failing. `disable iff (rst) !sig` over the four
// ticks passes at 1, is disabled at 2 and 4, where rst is high, and fails at
// 3, where sig is high with rst low: one pass and one failure, where without
// the clause the failures at 2 and 3 make two of each.
TEST(DeclaringProperties, DisableIffDisablesTheAttempt) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      PropertySource(std::string("  a: assert property (@(posedge clk) "
                                 "disable iff (rst) !sig)") +
                     kCounting),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  SimFixture g;
  auto* plain = RunAndFindVar(
      PropertySource(std::string("  a: assert property (@(posedge clk) !sig)") +
                     kCounting),
      g, "passes");
  ASSERT_NE(plain, nullptr);
  EXPECT_EQ(plain->value.ToUint64(), 2u);
  EXPECT_EQ(g.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

// §16.12: the disable condition reads the variables' current values, not
// sampled ones. live is set by a blocking assignment at the edge of tick 3,
// so the attempt at 3 is disabled though live's sampled value there is 0,
// and a property reading !live, sampled, passes at 3 and fails at 4.
TEST(DeclaringProperties, DisableConditionReadsTheCurrentValue) {
  const std::string kLive =
      "  logic live = 0;\n"
      "  always @(posedge clk) live = (tick == 3);\n";
  SimFixture f;
  auto* passes = RunAndFindVar(
      PropertySource(kLive +
                     "  a: assert property (@(posedge clk) disable iff (live) "
                     "!sig)" +
                     kCounting),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  SimFixture g;
  auto* sampled = RunAndFindVar(
      PropertySource(kLive + "  a: assert property (@(posedge clk) !live)" +
                     kCounting),
      g, "passes");
  ASSERT_NE(sampled, nullptr);
  EXPECT_EQ(sampled->value.ToUint64(), 3u);
  EXPECT_EQ(g.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

// §16.12: an instance of a named property with formal arguments is the
// property's body with the actuals substituted for the formals, its clock,
// disable condition and boolean alike; p_guarded(sig, rst) is the assertion
// above, one pass and one failure.
TEST(DeclaringProperties, InstanceActualsAreBoundToTheFormals) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      PropertySource(std::string("  property p_guarded(x, r);\n"
                                 "    @(posedge clk) disable iff (r) !x;\n"
                                 "  endproperty\n"
                                 "  a: assert property (p_guarded(sig, rst))") +
                     kCounting),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

// §16.12: a named property may be instantiated before its declaration.
TEST(DeclaringProperties, InstanceMayPrecedeTheDeclaration) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      PropertySource(std::string("  a: assert property (p_low(sig))") +
                     kCounting +
                     "  property p_low(x);\n"
                     "    @(posedge clk) !x;\n"
                     "  endproperty\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

}  // namespace
