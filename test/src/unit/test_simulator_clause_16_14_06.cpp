#include <gtest/gtest.h>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.14.6: "the assertion and the current values of all constant and
// automatic expressions appearing in its assertion arguments (see 16.14.6.1)
// are placed in a procedural assertion queue associated with the currently
// executing process.  Each of the entries in this queue is said to be a
// pending procedural assertion instance."  Observe that Enqueue grows the
// queue and that the entry retains its captured §16.5.1 SampledValue
// arguments without being matured yet.
TEST(ProceduralConcurrentAssertion, EnqueuePendingInstanceCapturesCurrentArgs) {
  ProceduralAssertionQueue q;
  EXPECT_EQ(q.Size(), 0u);

  PendingProceduralAssertion p;
  p.instance_name = "a1";
  p.kind = AssertionKind::kAssert;
  // §16.14.6 references §16.5.1: automatic / constant args captured by
  // current value (kCurrent), not Preponed.
  p.sampled_args.push_back(SampleAutomaticVariable(7));
  q.Enqueue(p);

  EXPECT_EQ(q.Size(), 1u);
  EXPECT_EQ(q.MaturedCount(), 0u);
  EXPECT_EQ(q.Entries().front().sampled_args.front().value, 7u);
  EXPECT_EQ(q.Entries().front().sampled_args.front().mode, SampleMode::kCurrent);
}

// §16.14.6: "In the Observed region of each simulation time step, each
// pending procedural assertion instance that is currently present in a
// procedural assertion queue shall mature, which means it is confirmed for
// execution."  Observe that MatureAll marks every pending instance matured.
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

// §16.14.6: "If a procedural assertion flush point (see 16.14.6.2) is
// reached in a process, its procedural assertion queue is cleared.  Any
// currently pending procedural assertion instances will not mature, unless
// again placed on the queue."  Observe that Flush empties the queue.
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

// §16.14.6: "Since any given statement in a procedure may be executed
// multiple times (as in a loop, for example), a particular procedural
// concurrent assertion may result in many pending procedural assertion
// instances within a single time step."  Observe that enqueuing the same
// instance name several times keeps every instance distinct in the queue.
TEST(ProceduralConcurrentAssertion, MultiplePendingInstancesPerTimeStep) {
  ProceduralAssertionQueue q;
  for (int i = 0; i < 5; ++i) {
    PendingProceduralAssertion p;
    p.instance_name = "loop_a";
    q.Enqueue(p);
  }
  EXPECT_EQ(q.Size(), 5u);
}

// §16.14.6: "a procedural assertion queue associated with the currently
// executing process".  Observe that SvaEngine hands out one queue per
// process identifier and that those queues are independent.
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

// §16.14.6: "A concurrent assertion statement that appears outside
// procedural code is referred to as a static concurrent assertion
// statement."  Observe that the predicate flips on the procedural
// context flag — a §16.5 module-item assertion is static, an embedded
// one (per §16.14.6 P1) is not.
TEST(ProceduralConcurrentAssertion, StaticConcurrentAssertionIsTheNonProceduralCase) {
  EXPECT_TRUE(IsStaticConcurrentAssertion(/*appears_in_procedural=*/false));
  EXPECT_FALSE(IsStaticConcurrentAssertion(/*appears_in_procedural=*/true));
}

// §16.14.6: "When a pending procedural assertion instance matures, if
// the current time step is one that corresponds to that assertion
// instance's leading clocking event, an evaluation attempt of the
// assertion begins immediately within the Observed region.  If the
// assertion's leading clocking event has not occurred in this time
// step, the matured instance shall be placed on the matured assertion
// queue, which will cause the assertion to begin an evaluation attempt
// upon the next clocking event."  Observe that placing into the matured
// queue retains the instance and that draining it yields the same
// instance for the next clocking event.
TEST(ProceduralConcurrentAssertion, MaturedQueueHoldsInstanceUntilNextClockTick) {
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

// §16.14.6: "It shall be illegal to use automatic variables in clocking
// events."  Observe that the predicate admits non-automatic carrying
// variables and rejects automatic ones.
TEST(ProceduralConcurrentAssertion, AutomaticVariableForbiddenInClockingEvent) {
  EXPECT_TRUE(IsAutomaticAllowedInClockingEvent(/*variable_is_automatic=*/false));
  EXPECT_FALSE(IsAutomaticAllowedInClockingEvent(/*variable_is_automatic=*/true));
}

// §16.14.6: "If no clocking event is specified in a procedural
// concurrent assertion, the leading clocking event of the assertion
// shall be inferred from the procedural context, if possible."  Observe
// that procedural-context clock wins over default clocking.
TEST(ProceduralConcurrentAssertion, ClockInferredFromProceduralContextFirst) {
  InferredClock c = InferClockForProceduralConcurrentAssertion(
      /*proc_context=*/"clk_proc",
      /*default=*/"clk_default");
  EXPECT_EQ(c.kind, InferredClockKind::kFromProceduralContext);
  EXPECT_EQ(c.signal_name, "clk_proc");
}

// §16.14.6: "If no clock can be inferred from the procedural context,
// then the clocks shall be inferred from the default clocking (see
// 14.12), as if the assertion were instantiated immediately before the
// procedure."  Observe the fallback to default clocking.
TEST(ProceduralConcurrentAssertion, ClockInferredFromDefaultClockingFallback) {
  InferredClock c = InferClockForProceduralConcurrentAssertion(
      /*proc_context=*/"",
      /*default=*/"clk_default");
  EXPECT_EQ(c.kind, InferredClockKind::kFromDefaultClocking);
  EXPECT_EQ(c.signal_name, "clk_default");
}

// §16.14.6: when neither procedural context nor default clocking
// supplies a clock, the inference fails.  This isn't a separate "shall"
// but is the implicit failure mode of the two preceding rules — the
// inference result must distinguish "no clock available" from a
// successfully inferred clock.
TEST(ProceduralConcurrentAssertion, ClockInferenceFailsWhenNoContextAvailable) {
  InferredClock c = InferClockForProceduralConcurrentAssertion(
      /*proc_context=*/"", /*default=*/"");
  EXPECT_EQ(c.kind, InferredClockKind::kNotInferrable);
  EXPECT_EQ(c.signal_name, "");
}

// §16.14.6: "A clock shall be inferred for the context of an always or
// initial procedure that satisfies the following requirements:
//   a) There is no blocking timing control in the procedure.
//   b) There is exactly one event control in the procedure.
//   c) One and only one event expression within the event control of
//      the procedure satisfies both of the following conditions ..."
// Observe that all three requirements must hold for inference to
// succeed.
TEST(ProceduralConcurrentAssertion, ClockInferenceRequiresAllThreeConditions) {
  // All three hold -> ok.
  EXPECT_TRUE(SatisfiesClockInferenceRequirements(true, true, true));
  // Any one missing -> failure.
  EXPECT_FALSE(SatisfiesClockInferenceRequirements(false, true, true));
  EXPECT_FALSE(SatisfiesClockInferenceRequirements(true, false, true));
  EXPECT_FALSE(SatisfiesClockInferenceRequirements(true, true, false));
  // None hold -> failure.
  EXPECT_FALSE(SatisfiesClockInferenceRequirements(false, false, false));
}

}  // namespace
