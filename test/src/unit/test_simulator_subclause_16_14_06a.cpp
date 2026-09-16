#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"

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

// §16.14.6 has a concurrent assertion embedded in procedural code "evaluated as
// though it were a separate concurrent assertion". The property here carries no
// clocking event of its own, so it takes the clocking of the procedure that
// reaches it -- the posedge the always block waits on -- and `a` is false when
// that edge arrives, so the assertion fails and §16.3's default report says so.
//
// The parser discarded the property before reading it, so what the executor
// evaluated was nothing at all. The pair below is what says the property is
// read: a case asserting only the failure passes on an evaluation that answers
// false for every source, which is what a discarded property gives it.
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

// The other half of the pair: a property that holds reports nothing. This is
// the case a discarded property cannot pass, the null it left behind being
// evaluated as false at every edge.
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

// §16.5: "Concurrent assertions ... are evaluated in the Observed region", and
// §16.14.6 has an embedded one "evaluated as though it were a separate
// concurrent assertion", so the region is the same wherever the statement is
// written. §4.4 orders the Observed region after the whole active region set,
// so a design that writes at the same clock edge has written by the time the
// property is evaluated.
//
// `peek()` is what makes the region visible. §16.5.1's sampling covers the
// variables a property names, and this one names none: a function call reads
// `v` from within its body, where no sample stands, so the property reads the
// live value and answers differently in the two regions. Evaluated where the
// statement stands -- the Active region, in the middle of the write that
// assigned the clock -- it read the 0 `v` still held and the assertion failed.
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

// The other half: the property is still evaluated, and still fails when what it
// reads has not arrived. `v` is written a time step after the edge rather than
// at it, so no region of the tick's own time slot sees the 1 and the assertion
// takes its fail action. A property that stopped being evaluated at all, or one
// answered true for everything, passes the case above and fails this.
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

// The form that already answered from the Observed region, asserted unchanged:
// §16.14.5's static concurrent assertion is carried by a process the scheduler
// resumes there, and it reads the same 1 the embedded form now reads. The pair
// says the two spellings of one assertion agree.
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
