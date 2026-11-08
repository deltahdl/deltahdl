#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sampling.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SvaEngineAbort, AcceptForcesTrueOnConditionElseInner) {
  EXPECT_EQ(EvalAbortAccept(true, PropertyResult::kFail),
            PropertyResult::kPass);
  EXPECT_EQ(EvalAbortAccept(false, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalAbortAccept(false, PropertyResult::kPass),
            PropertyResult::kPass);
}

TEST(SvaEngineAbort, RejectForcesFalseOnConditionElseInner) {
  EXPECT_EQ(EvalAbortReject(true, PropertyResult::kPass),
            PropertyResult::kFail);
  EXPECT_EQ(EvalAbortReject(false, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalAbortReject(false, PropertyResult::kFail),
            PropertyResult::kFail);
}

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

TEST(SvaEngineAbort, NotInvertsAbortOperatorEffect) {
  EXPECT_EQ(EvalPropertyNot(EvalAbortAccept(true, PropertyResult::kFail)),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyNot(EvalAbortAccept(false, PropertyResult::kPass)),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyNot(EvalAbortAccept(false, PropertyResult::kFail)),
            PropertyResult::kPass);
}

TEST(SvaEngineAbort, NestedOutermostOperatorTakesPrecedence) {
  EXPECT_EQ(EvalNestedAbort(true, true, false, true, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalNestedAbort(true, false, false, true, PropertyResult::kPass),
            PropertyResult::kFail);
}

TEST(SvaEngineAbort, AbortConditionUsesSampledValuesUnlikeDisableIff) {
  EXPECT_TRUE(AbortConditionUsesSampledValues());
  EXPECT_TRUE(DisableConditionUsesCurrentValues());
}

TEST(SvaEngineAbort, SynchronousAbortEvaluatesOnlyAtClockingEvent) {
  EXPECT_FALSE(AbortConditionEvaluatedAtClockingEventOnly(false));
  EXPECT_TRUE(AbortConditionEvaluatedAtClockingEventOnly(true));
}

TEST(SvaEngineAbort, AbortPreservesVacuousInnerWhenConditionFalse) {
  EXPECT_EQ(EvalAbortAccept(false, PropertyResult::kVacuousPass),
            PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalAbortReject(false, PropertyResult::kVacuousPass),
            PropertyResult::kVacuousPass);
}

TEST(SvaEngineAbort, NestedAbortWithNeitherConditionYieldsInnerProperty) {
  EXPECT_EQ(EvalNestedAbort(true, false, false, false, PropertyResult::kPass),
            PropertyResult::kPass);
  EXPECT_EQ(EvalNestedAbort(true, false, false, false, PropertyResult::kFail),
            PropertyResult::kFail);
}

TEST(SvaEngineAbort, AbortTakesPrecedenceUnderConjunction) {
  EXPECT_EQ(EvalPropertyAnd(EvalAbortAccept(true, PropertyResult::kFail),
                            EvalAbortReject(false, PropertyResult::kPass)),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyAnd(EvalAbortAccept(false, PropertyResult::kPass),
                            EvalAbortReject(true, PropertyResult::kPass)),
            PropertyResult::kFail);
}

TEST(SvaEngineAbort, AbortTakesPrecedenceUnderDisjunction) {
  EXPECT_EQ(EvalPropertyOr(EvalAbortAccept(true, PropertyResult::kFail),
                           EvalAbortReject(false, PropertyResult::kFail)),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyOr(EvalAbortAccept(false, PropertyResult::kPass),
                           EvalAbortReject(true, PropertyResult::kPass)),
            PropertyResult::kPass);
}

TEST(SvaEngineAbort, NestedRejectOuterOverridesAcceptInner) {
  EXPECT_EQ(EvalNestedAbort(false, true, true, true, PropertyResult::kPass),
            PropertyResult::kFail);
  EXPECT_EQ(EvalNestedAbort(false, false, true, true, PropertyResult::kFail),
            PropertyResult::kPass);
}

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
