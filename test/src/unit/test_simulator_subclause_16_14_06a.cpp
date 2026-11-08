#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine_queues.h"
#include "simulator/sva_engine_sampling.h"

using namespace delta;

namespace {

TEST(ProceduralConcurrentAssertion, EnqueuePendingInstanceCapturesCurrentArgs) {
  ProceduralAssertionQueue q;
  EXPECT_EQ(q.Size(), 0u);

  PendingProceduralAssertion p;
  p.instance_name = "a1";
  p.kind = AssertionKind::kAssert;

  p.sampled_args.push_back(SampleAutomaticVariable(7));
  q.Enqueue(p);

  EXPECT_EQ(q.Size(), 1u);
  EXPECT_EQ(q.MaturedCount(), 0u);
  EXPECT_EQ(q.Entries().front().sampled_args.front().value, 7u);
  EXPECT_EQ(q.Entries().front().sampled_args.front().mode,
            SampleMode::kCurrent);
}

TEST(ProceduralConcurrentAssertion, MatureAllConfirmsEveryPendingInstance) {
  ProceduralAssertionQueue q;
  for (int i = 0; i < 3; ++i) {
    PendingProceduralAssertion p;
    p.instance_name = "p" + std::to_string(i);
    q.Enqueue(p);
  }
  EXPECT_EQ(q.MaturedCount(), 0u);

  q.MatureAll();

  EXPECT_EQ(q.MaturedCount(), 3u);
  for (const auto& e : q.Entries()) {
    EXPECT_TRUE(e.matured);
  }
}

TEST(ProceduralConcurrentAssertion, FlushClearsQueueSoNothingMatures) {
  ProceduralAssertionQueue q;
  PendingProceduralAssertion p;
  p.instance_name = "a";
  q.Enqueue(p);
  EXPECT_EQ(q.Size(), 1u);

  q.Flush();

  EXPECT_EQ(q.Size(), 0u);
  EXPECT_EQ(q.MaturedCount(), 0u);
}

TEST(ProceduralConcurrentAssertion, MultiplePendingInstancesPerTimeStep) {
  ProceduralAssertionQueue q;
  for (int i = 0; i < 5; ++i) {
    PendingProceduralAssertion p;
    p.instance_name = "loop_a";
    q.Enqueue(p);
  }
  EXPECT_EQ(q.Size(), 5u);
}

TEST(ProceduralConcurrentAssertion, EngineProvidesQueuePerProcess) {
  SvaEngine eng;
  auto& q1 = eng.GetProceduralQueue("proc1");
  auto& q2 = eng.GetProceduralQueue("proc2");

  PendingProceduralAssertion p;
  p.instance_name = "x";
  q1.Enqueue(p);

  EXPECT_EQ(q1.Size(), 1u);
  EXPECT_EQ(q2.Size(), 0u);
}

TEST(ProceduralConcurrentAssertion,
     StaticConcurrentAssertionIsTheNonProceduralCase) {
  EXPECT_TRUE(IsStaticConcurrentAssertion(false));
  EXPECT_FALSE(IsStaticConcurrentAssertion(true));
}

TEST(ProceduralConcurrentAssertion,
     MaturedQueueHoldsInstanceUntilNextClockTick) {
  MaturedAssertionQueue mq;
  EXPECT_EQ(mq.Size(), 0u);

  PendingProceduralAssertion p;
  p.instance_name = "waiting_for_clock";
  mq.Place(p);
  EXPECT_EQ(mq.Size(), 1u);

  auto drained = mq.TakeAll();
  EXPECT_EQ(drained.size(), 1u);
  EXPECT_TRUE(drained.front().matured);
  EXPECT_EQ(drained.front().instance_name, "waiting_for_clock");
  EXPECT_EQ(mq.Size(), 0u);
}

TEST(ProceduralConcurrentAssertion, AutomaticVariableForbiddenInClockingEvent) {
  EXPECT_TRUE(IsAutomaticAllowedInClockingEvent(false));
  EXPECT_FALSE(IsAutomaticAllowedInClockingEvent(true));
}

TEST(ProceduralConcurrentAssertion, ClockInferredFromProceduralContextFirst) {
  InferredClock c =
      InferClockForProceduralConcurrentAssertion("clk_proc", "clk_default");
  EXPECT_EQ(c.kind, InferredClockKind::kFromProceduralContext);
  EXPECT_EQ(c.signal_name, "clk_proc");
}

TEST(ProceduralConcurrentAssertion, ClockInferredFromDefaultClockingFallback) {
  InferredClock c =
      InferClockForProceduralConcurrentAssertion("", "clk_default");
  EXPECT_EQ(c.kind, InferredClockKind::kFromDefaultClocking);
  EXPECT_EQ(c.signal_name, "clk_default");
}

TEST(ProceduralConcurrentAssertion, ClockInferenceFailsWhenNoContextAvailable) {
  InferredClock c = InferClockForProceduralConcurrentAssertion("", "");
  EXPECT_EQ(c.kind, InferredClockKind::kNotInferrable);
  EXPECT_EQ(c.signal_name, "");
}

TEST(ProceduralConcurrentAssertion, ClockInferenceRequiresAllThreeConditions) {
  EXPECT_TRUE(SatisfiesClockInferenceRequirements(true, true, true));

  EXPECT_FALSE(SatisfiesClockInferenceRequirements(false, true, true));
  EXPECT_FALSE(SatisfiesClockInferenceRequirements(true, false, true));
  EXPECT_FALSE(SatisfiesClockInferenceRequirements(true, true, false));

  EXPECT_FALSE(SatisfiesClockInferenceRequirements(false, false, false));
}

TEST(ProceduralConcurrentAssertionSim, FalseBooleanPropertyFailsAtTheEdge) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic a = 0;\n"
      "  always @(posedge clk) assert property (a);\n"
      "  initial #1 clk = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "Assertion failed.");
}

TEST(ProceduralConcurrentAssertionSim, TrueBooleanPropertyReportsNothing) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic a = 1;\n"
      "  always @(posedge clk) assert property (a);\n"
      "  initial #1 clk = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "");
}

TEST(ProceduralConcurrentAssertionSim, PropertyIsEvaluatedInTheObservedRegion) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0;\n"
      "  int v = 0;\n"
      "  int saw = 99;\n"
      "  function int peek();\n"
      "    return v;\n"
      "  endfunction\n"
      "  always @(posedge clk) assert property (peek() == 1) saw = 1;\n"
      "  else saw = 0;\n"
      "  always @(posedge clk) v = 1;\n"
      "  initial #5 clk = 1;\n"
      "endmodule\n",
      f, "saw");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ProceduralConcurrentAssertionSim,
     PropertyStillFailsOnWhatTheTickCannotSee) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0;\n"
      "  int v = 0;\n"
      "  int saw = 99;\n"
      "  function int peek();\n"
      "    return v;\n"
      "  endfunction\n"
      "  always @(posedge clk) assert property (peek() == 1) saw = 1;\n"
      "  else saw = 0;\n"
      "  initial begin\n"
      "    #5 clk = 1;\n"
      "    #5 v = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "saw");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(ProceduralConcurrentAssertionSim, StaticFormReadsTheSameValueAtTheEdge) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0;\n"
      "  int v = 0;\n"
      "  int saw = 99;\n"
      "  function int peek();\n"
      "    return v;\n"
      "  endfunction\n"
      "  assert property (@(posedge clk) peek() == 1) saw = 1;\n"
      "  else saw = 0;\n"
      "  always @(posedge clk) v = 1;\n"
      "  initial #5 clk = 1;\n"
      "endmodule\n",
      f, "saw");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
