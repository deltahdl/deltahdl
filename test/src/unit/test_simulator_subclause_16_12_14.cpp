#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sva_engine.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §16.12.14: for an accept abort (accept_on / sync_accept_on) the overall
// evaluation is true when the abort condition becomes true; otherwise it equals
// the underlying property_expr's verdict. The true-condition case also shows
// the abort taking precedence over a contrary settled verdict (here kFail).
TEST(SvaEngineAbort, AcceptForcesTrueOnConditionElseInner) {
  EXPECT_EQ(EvalAbortAccept(/*abort_condition=*/true, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalAbortAccept(/*abort_condition=*/false, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalAbortAccept(/*abort_condition=*/false, PropertyResult::kPass),
            PropertyResult::kPass);
}

// §16.12.14: for a reject abort (reject_on / sync_reject_on) the overall
// evaluation is false when the abort condition becomes true; otherwise it
// equals the underlying property_expr's verdict. The true-condition case also
// shows the abort taking precedence over a contrary settled verdict (here
// kPass).
TEST(SvaEngineAbort, RejectForcesFalseOnConditionElseInner) {
  EXPECT_EQ(EvalAbortReject(/*abort_condition=*/true, PropertyResult::kPass),
            PropertyResult::kFail);
  EXPECT_EQ(EvalAbortReject(/*abort_condition=*/false, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalAbortReject(/*abort_condition=*/false, PropertyResult::kFail),
            PropertyResult::kFail);
}

// §16.12.14: reject_on(c) p is the same as not(accept_on(c) not p). The reject
// helper agrees with that equivalence for the definite verdicts.
TEST(SvaEngineAbort, RejectIsDualOfAccept) {
  for (bool cond : {false, true}) {
    for (PropertyResult inner :
         {PropertyResult::kPass, PropertyResult::kFail}) {
      PropertyResult dual =
          EvalPropertyNot(EvalAbortAccept(cond, EvalPropertyNot(inner)));
      EXPECT_EQ(EvalAbortReject(cond, inner), dual);
    }
  }
}

// §16.12.14: `not` inverts the effect of the abort operator. For the standard's
// example `not (accept_on(a) p1)`, when a becomes true while evaluating p1 the
// accept_on forces its term true and the enclosing not flips the whole property
// to false; with a quiet, the not simply inverts p1's own verdict. This is the
// abort helper composed under EvalPropertyNot with a plain underlying property
// (distinct from the reject-dual shape, which nots the inner argument too).
TEST(SvaEngineAbort, NotInvertsAbortOperatorEffect) {
  // a true during p1: accept_on forces the term true even over a failing p1, so
  // the enclosing not yields false.
  EXPECT_EQ(EvalPropertyNot(EvalAbortAccept(/*abort_condition=*/true,
                                            PropertyResult::kFail)),
            PropertyResult::kFail);
  // a quiet: not simply inverts the underlying property_expr verdict.
  EXPECT_EQ(EvalPropertyNot(EvalAbortAccept(/*abort_condition=*/false,
                                            PropertyResult::kPass)),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyNot(EvalAbortAccept(/*abort_condition=*/false,
                                            PropertyResult::kFail)),
            PropertyResult::kPass);
}

// §16.12.14: nested abort operators are evaluated in lexical order with the
// outermost taking precedence. For `accept_on(a) reject_on(b) p1`, when a and b
// become true in the same time step p succeeds; when only the inner condition b
// is true p fails.
TEST(SvaEngineAbort, NestedOutermostOperatorTakesPrecedence) {
  // accept_on (outer, forces true) wrapping reject_on (inner, forces false).
  EXPECT_EQ(
      EvalNestedAbort(/*outer_forces_true=*/true, /*outer_condition=*/true,
                      /*inner_forces_true=*/false, /*inner_condition=*/true,
                      PropertyResult::kPass),
      PropertyResult::kPass);
  // Inner reject condition true, outer accept condition not yet true: p fails.
  EXPECT_EQ(
      EvalNestedAbort(/*outer_forces_true=*/true, /*outer_condition=*/false,
                      /*inner_forces_true=*/false, /*inner_condition=*/true,
                      PropertyResult::kPass),
      PropertyResult::kFail);
}

// §16.12.14: the abort condition is evaluated using sampled values as a regular
// Boolean expression, unlike disable iff, whose condition uses current values.
TEST(SvaEngineAbort, AbortConditionUsesSampledValuesUnlikeDisableIff) {
  EXPECT_TRUE(AbortConditionUsesSampledValues());
  // disable iff evaluates its condition with current values — the contrasting
  // rule §16.12.14 calls out for the abort condition.
  EXPECT_TRUE(DisableConditionUsesCurrentValues());
}

// §16.12.14: asynchronous abort operators are evaluated at every simulation
// time step; the synchronous operators are evaluated only when the clocking
// event happens.
TEST(SvaEngineAbort, SynchronousAbortEvaluatesOnlyAtClockingEvent) {
  EXPECT_FALSE(
      AbortConditionEvaluatedAtClockingEventOnly(/*synchronous_abort=*/false));
  EXPECT_TRUE(
      AbortConditionEvaluatedAtClockingEventOnly(/*synchronous_abort=*/true));
}

// §16.12.14 (edge case): when the abort condition does not become true the
// result equals the underlying property_expr's verdict exactly — including a
// vacuous pass, which is neither forced to a plain pass nor to a fail.
TEST(SvaEngineAbort, AbortPreservesVacuousInnerWhenConditionFalse) {
  EXPECT_EQ(
      EvalAbortAccept(/*abort_condition=*/false, PropertyResult::kVacuousPass),
      PropertyResult::kVacuousPass);
  EXPECT_EQ(
      EvalAbortReject(/*abort_condition=*/false, PropertyResult::kVacuousPass),
      PropertyResult::kVacuousPass);
}

// §16.12.14 (edge case): with neither nested abort condition true, both
// operators are quiet and the underlying property_expr verdict passes straight
// through, whatever it is.
TEST(SvaEngineAbort, NestedAbortWithNeitherConditionYieldsInnerProperty) {
  EXPECT_EQ(
      EvalNestedAbort(/*outer_forces_true=*/true, /*outer_condition=*/false,
                      /*inner_forces_true=*/false, /*inner_condition=*/false,
                      PropertyResult::kPass),
      PropertyResult::kPass);
  EXPECT_EQ(
      EvalNestedAbort(/*outer_forces_true=*/true, /*outer_condition=*/false,
                      /*inner_forces_true=*/false, /*inner_condition=*/false,
                      PropertyResult::kFail),
      PropertyResult::kFail);
}

// §16.12.14: when the abort condition occurs at the same time step where the
// evaluation of the property_expr ends, the abort takes precedence. The
// standard shows this with `(accept_on(a) p1) and (reject_on(b) p2)`: if a
// becomes true during p1 the first term is ignored in deciding the truth of p
// (so the verdict follows the second term), and if b becomes true during p2
// then p evaluates to false. Composing the abort helpers under EvalPropertyAnd
// reproduces both outcomes.
TEST(SvaEngineAbort, AbortTakesPrecedenceUnderConjunction) {
  // a true during p1: accept_on forces the first term true even though p1's own
  // verdict would fail, so the first term is ignored and p follows the second
  // (reject_on quiet, its underlying p2 passing) -> pass.
  EXPECT_EQ(
      EvalPropertyAnd(
          EvalAbortAccept(/*abort_condition=*/true, PropertyResult::kFail),
          EvalAbortReject(/*abort_condition=*/false, PropertyResult::kPass)),
      PropertyResult::kPass);
  // b true during p2: reject_on forces the second term false, which the
  // conjunction propagates regardless of the first term -> p evaluates false.
  EXPECT_EQ(
      EvalPropertyAnd(
          EvalAbortAccept(/*abort_condition=*/false, PropertyResult::kPass),
          EvalAbortReject(/*abort_condition=*/true, PropertyResult::kPass)),
      PropertyResult::kFail);
}

// §16.12.14: the companion example `(accept_on(a) p1) or (reject_on(b) p2)`: if
// a becomes true during p1 then p evaluates to true, and if b becomes true
// during p2 then the second term is ignored (the verdict follows the first
// term). Composing the abort helpers under EvalPropertyOr reproduces both.
TEST(SvaEngineAbort, AbortTakesPrecedenceUnderDisjunction) {
  // a true during p1: accept_on forces the first term true, and the disjunction
  // holds on either operand holding -> p evaluates true even with p1 failing.
  EXPECT_EQ(
      EvalPropertyOr(
          EvalAbortAccept(/*abort_condition=*/true, PropertyResult::kFail),
          EvalAbortReject(/*abort_condition=*/false, PropertyResult::kFail)),
      PropertyResult::kPass);
  // b true during p2: reject_on forces the second term false, so the second
  // term is ignored and p follows the first (accept_on quiet, p1 passing).
  EXPECT_EQ(
      EvalPropertyOr(
          EvalAbortAccept(/*abort_condition=*/false, PropertyResult::kPass),
          EvalAbortReject(/*abort_condition=*/true, PropertyResult::kPass)),
      PropertyResult::kPass);
}

// §16.12.14 (edge case): the outermost-precedence rule holds for the opposite
// polarity arrangement too. For `reject_on(a) accept_on(b) p1`, when both a and
// b fire the outer reject decides the verdict (fail); when only the inner
// accept fires it forces a pass even over a failing underlying property_expr.
TEST(SvaEngineAbort, NestedRejectOuterOverridesAcceptInner) {
  EXPECT_EQ(
      EvalNestedAbort(/*outer_forces_true=*/false, /*outer_condition=*/true,
                      /*inner_forces_true=*/true, /*inner_condition=*/true,
                      PropertyResult::kPass),
      PropertyResult::kFail);
  EXPECT_EQ(
      EvalNestedAbort(/*outer_forces_true=*/false, /*outer_condition=*/false,
                      /*inner_forces_true=*/true, /*inner_condition=*/true,
                      PropertyResult::kFail),
      PropertyResult::kPass);
}

// --- Live cases: abort properties over real source ---

// The module the cases share: clk rises at 5, 15, ..., 75, tick n at
// 10n - 5, the tick counter counting through eight ticks; go is high at
// tick 1, get at 2 and 3, put at 4 and 6, stop at 5, flag at 2 and both at
// 3, stop_async is high from 47 to 49 alone, between the ticks at 45 and
// 55, and nv is low throughout. `items` declare the assertions, counting in
// `passes` and `fails`.
std::string AbortSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic go, get, put, stop, flag, both, nv;\n"
         "  logic stop_async = 0;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign go = tick inside {1};\n"
         "  assign get = tick inside {2, 3};\n"
         "  assign put = tick inside {4, 6};\n"
         "  assign stop = tick inside {5};\n"
         "  assign flag = tick inside {2};\n"
         "  assign both = tick inside {3};\n"
         "  assign nv = 0;\n"
         "  initial begin\n"
         "    #47 stop_async = 1;\n"
         "    #2 stop_async = 0;\n"
         "  end\n" +
         items +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

// §16.12.14: the clause's assertion in its synchronous form, `go ##1
// get[*2] |-> sync_reject_on(stop) put[->2]`: the attempt from 1 has its
// consequent begin at 3, put holds at 4 and stop at 5, checked at the tick,
// so the reject makes the consequent false and the attempt fails at 5; the
// seven other attempts, go low, are true.
TEST(AbortProperty, SynchronousRejectReadsTheConditionAtTheTicks) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      AbortSource("  p: assert property (@(posedge clk) go ##1 get[*2] |-> "
                  "sync_reject_on(stop) put[->2]) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 7u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

// §16.12.14: `reject_on(stop_async)` checks its condition at every time
// step, so the pulse between the ticks at 45 and 55 aborts the consequent,
// which fails at 6, where `sync_reject_on(stop_async)`, reading the
// condition at the ticks alone, never sees it and put[->2] matches at 6.
TEST(AbortProperty, AsynchronousRejectSeesAChangeBetweenTicks) {
  SimFixture f;
  auto* async_fails = RunAndFindVar(
      AbortSource("  p: assert property (@(posedge clk) go ##1 get[*2] |-> "
                  "reject_on(stop_async) put[->2]) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(async_fails, nullptr);
  EXPECT_EQ(async_fails->value.ToUint64(), 7u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  SimFixture g;
  auto* sync_holds = RunAndFindVar(
      AbortSource("  p: assert property (@(posedge clk) go ##1 get[*2] |-> "
                  "sync_reject_on(stop_async) put[->2]) passes++; else "
                  "fails++;\n"),
      g, "passes");
  ASSERT_NE(sync_holds, nullptr);
  EXPECT_EQ(sync_holds->value.ToUint64(), 8u);
  EXPECT_EQ(g.ctx.FindVariable("fails")->value.ToUint64(), 0u);
}

// §16.12.14: `sync_accept_on(flag) nv` is true at the tick flag holds at,
// nv false notwithstanding, and its operand otherwise: one pass and seven
// failures; `not (sync_accept_on(flag) nv)` inverts the effect.
TEST(AbortProperty, AcceptMakesThePropertyTrueAndNotInvertsIt) {
  SimFixture f;
  auto* accepts = RunAndFindVar(
      AbortSource("  p: assert property (@(posedge clk) sync_accept_on(flag) "
                  "nv) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(accepts, nullptr);
  EXPECT_EQ(accepts->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 7u);
  SimFixture g;
  auto* inverted = RunAndFindVar(
      AbortSource("  p: assert property (@(posedge clk) not "
                  "(sync_accept_on(flag) nv)) passes++; else fails++;\n"),
      g, "passes");
  ASSERT_NE(inverted, nullptr);
  EXPECT_EQ(inverted->value.ToUint64(), 7u);
  EXPECT_EQ(g.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

// §16.12.14: nested aborts whose conditions become true in the same time
// step are decided by the outermost: `sync_accept_on(both)
// sync_reject_on(both) nv` is true at 3, and `sync_reject_on(both)
// sync_accept_on(both) nv` false there.
TEST(AbortProperty, TheOutermostOfNestedAbortsTakesPrecedence) {
  SimFixture f;
  auto* accept_outer = RunAndFindVar(
      AbortSource("  p: assert property (@(posedge clk) sync_accept_on(both) "
                  "sync_reject_on(both) nv) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(accept_outer, nullptr);
  EXPECT_EQ(accept_outer->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 7u);
  SimFixture g;
  auto* reject_outer = RunAndFindVar(
      AbortSource("  p: assert property (@(posedge clk) sync_reject_on(both) "
                  "sync_accept_on(both) nv) passes++; else fails++;\n"),
      g, "passes");
  ASSERT_NE(reject_outer, nullptr);
  EXPECT_EQ(reject_outer->value.ToUint64(), 0u);
  EXPECT_EQ(g.ctx.FindVariable("fails")->value.ToUint64(), 8u);
}

}  // namespace
