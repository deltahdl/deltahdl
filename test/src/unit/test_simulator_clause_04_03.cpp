#include <gtest/gtest.h>

#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"
#include "simulator/vpi.h"

using namespace delta;

// §4.3 ¶1: "The SystemVerilog language is defined in terms of a discrete event
// execution model." A discrete event model advances simulation time only when
// scheduled events fire — between events, time is stationary. The Scheduler's
// Run() loop drains the event_calendar_ in time-key order, so an empty calendar
// leaves CurrentTime unchanged and an event scheduled at a future time fires at
// exactly that time.
TEST(EventSimulationSim, DiscreteEventModelTimeAdvancesOnlyOnScheduledEvents) {
  Arena arena;
  Scheduler sched(arena);

  EXPECT_EQ(sched.CurrentTime().ticks, 0u);
  sched.Run();
  EXPECT_EQ(sched.CurrentTime().ticks, 0u);

  uint64_t observed_time = UINT64_MAX;
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { observed_time = sched.CurrentTime().ticks; };
  sched.ScheduleEvent({42}, Region::kActive, ev);

  sched.Run();
  EXPECT_EQ(observed_time, 42u);
  EXPECT_EQ(sched.CurrentTime().ticks, 42u);
}

// §4.3 ¶2: "Examples of processes include, but are not limited to, primitives;
// initial, always, always_comb, always_latch, and always_ff procedures;
// continuous assignments; ...". Each procedural process kind enumerated in the
// LRM has a corresponding ProcessKind value, and the kind is preserved on the
// Process objects the simulator schedules.
TEST(EventSimulationSim, ProcessKindCoversLrmEnumeratedExamples) {
  EXPECT_NE(static_cast<int>(ProcessKind::kInitial),
            static_cast<int>(ProcessKind::kAlways));
  EXPECT_NE(static_cast<int>(ProcessKind::kAlways),
            static_cast<int>(ProcessKind::kAlwaysComb));
  EXPECT_NE(static_cast<int>(ProcessKind::kAlwaysComb),
            static_cast<int>(ProcessKind::kAlwaysLatch));
  EXPECT_NE(static_cast<int>(ProcessKind::kAlwaysLatch),
            static_cast<int>(ProcessKind::kAlwaysFF));
  EXPECT_NE(static_cast<int>(ProcessKind::kInitial),
            static_cast<int>(ProcessKind::kContAssign));
}

// §4.3 ¶2: "Processes are objects that can be evaluated, that can have state,
// and that can respond to changes on their inputs to produce outputs." An
// initial procedure is an object with state (the variable it writes) that
// produces an output when evaluated.
TEST(EventSimulationSim, InitialProcedureIsAnEvaluatedProcess) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd42;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 42u);
}

// §4.3 ¶3: "Every change in state of a net or variable in the system
// description being simulated is considered an *update event*."
// `ScheduleNonblockingAssign` labels its scheduled event with
// EventKind::kUpdate. The Scheduler tallies update-labelled events at schedule
// time, so a successful NBA path must produce a non-zero update-event tally.
TEST(EventSimulationSim, NbaAssignmentSchedulesAnUpdateEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst;\n"
      "  initial dst <= 8'd9;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  EXPECT_EQ(f.scheduler.UpdateEventScheduledCount(), 0u);
  f.scheduler.Run();
  EXPECT_GE(f.scheduler.UpdateEventScheduledCount(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 9u);
}

// §4.3 ¶3 corollary: a design that performs no state changes must produce no
// update events. An empty module with no nets, variables, or procedures
// schedules no events at all, let alone update-labelled ones.
TEST(EventSimulationSim, NoStateChangeMeansNoUpdateEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.scheduler.UpdateEventScheduledCount(), 0u);
}

// §4.3 ¶4 sentence 1: "Processes are sensitive to update events. When an
// update event is executed, all the processes that are sensitive to that event
// are considered for evaluation in an arbitrary order." Two `always_comb`
// procedures sensitive to the same source must both re-evaluate when the
// source changes, regardless of the order the simulator picks.
TEST(EventSimulationSim, AllSensitiveProcessesEvaluateOnUpdateEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, a, b;\n"
      "  initial src = 8'd5;\n"
      "  always_comb a = src + 8'd1;\n"
      "  always_comb b = src + 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 7u);
}

// §4.3 ¶4 sentence 2: "The evaluation of a process is also an event, known as
// an *evaluation event*." `ScheduleProcess` (lowerer.cpp) labels each process
// scheduling with EventKind::kEvaluation, so lowering a design that contains
// procedural processes must register evaluation events with the scheduler.
TEST(EventSimulationSim, ProcessEvaluationSchedulesAnEvaluationEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  EXPECT_GE(f.scheduler.EvaluationEventScheduledCount(), 1u);
}

// §4.3 ¶4: update and evaluation events are distinct kinds. The two counters
// the Scheduler exposes count disjoint sets of events — an event is one or the
// other at schedule time, never both.
TEST(EventSimulationSim, UpdateAndEvaluationEventsAreDistinctKinds) {
  Arena arena;
  Scheduler sched(arena);

  auto* update = sched.GetEventPool().Acquire();
  update->kind = EventKind::kUpdate;
  update->callback = []() {};
  sched.ScheduleEvent({0}, Region::kNBA, update);

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = []() {};
  sched.ScheduleEvent({0}, Region::kActive, eval);

  EXPECT_EQ(sched.UpdateEventScheduledCount(), 1u);
  EXPECT_EQ(sched.EvaluationEventScheduledCount(), 1u);
}

// §4.3 ¶5: "Evaluation events also include PLI callbacks, which are points in
// the execution model where PLI application routines can be called from the
// simulation kernel." `RegionForPliCallback` returns the assigned region for
// each one-shot PLI callback in §4.10 Table 4-1; that mapping is the
// production-side hook that places PLI callbacks into the same event regions
// the simulator drains. cbReadOnlySynch landing in Postponed and cbAfterDelay
// landing in Pre-Active demonstrates that PLI callbacks are scheduled as
// regular regional events alongside other evaluation events.
TEST(EventSimulationSim, PliCallbacksAreScheduledAsRegionalEvaluationEvents) {
  EXPECT_TRUE(IsOneShotPliCallback(kCbAfterDelay));
  EXPECT_NE(RegionForPliCallback(kCbAfterDelay), Region::kCOUNT);
  EXPECT_NE(RegionForPliCallback(kCbReadOnlySynch), Region::kCOUNT);
  EXPECT_NE(RegionForPliCallback(kCbAtEndOfSimTime), Region::kCOUNT);
}

// §4.3 ¶5 cross-check: the default kind of a freshly acquired Event is
// kEvaluation, matching the LRM classification of PLI callbacks (and any other
// non-update scheduled event) as evaluation events. EventPool::Release also
// resets the kind to kEvaluation, so recycled events default to the evaluation
// classification.
TEST(EventSimulationSim, FreshlyAcquiredEventDefaultsToEvaluationKind) {
  Arena arena;
  EventPool pool(arena);
  auto* ev = pool.Acquire();
  EXPECT_EQ(ev->kind, EventKind::kEvaluation);
  ev->kind = EventKind::kUpdate;
  pool.Release(ev);
  auto* recycled = pool.Acquire();
  EXPECT_EQ(recycled->kind, EventKind::kEvaluation);
}

// §4.3 ¶6: "The term *simulation time* is used to refer to the time value
// maintained by the simulator to model the actual time it would take for the
// system description being simulated. The term *time* is used interchangeably
// with simulation time in this clause." The Scheduler's CurrentTime() exposes
// that maintained time value; it advances exactly to the time of the next
// firing event.
TEST(EventSimulationSim, SchedulerMaintainsSimulationTime) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> observed_times;

  for (uint64_t t : {0, 5, 17}) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&observed_times, &sched]() {
      observed_times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kActive, ev);
  }
  sched.Run();
  ASSERT_EQ(observed_times.size(), 3u);
  EXPECT_EQ(observed_times[0], 0u);
  EXPECT_EQ(observed_times[1], 5u);
  EXPECT_EQ(observed_times[2], 17u);
}

// §4.3 ¶7: "To fully support clear and predictable interactions, a single time
// slot is divided into multiple regions where events can be scheduled that
// provide for an ordering of particular types of execution." The `Region` enum
// declares the multi-region division; events scheduled in earlier regions of a
// time slot run before events scheduled in later regions of the same slot.
TEST(EventSimulationSim, SingleTimeSlotIsDividedIntoOrderedRegions) {
  EXPECT_GT(kRegionCount, 1u);

  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { order.push_back("nba"); };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { order.push_back("active"); };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "nba");
}
