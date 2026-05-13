#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

// §4.4 ¶1: "A compliant SystemVerilog simulator shall maintain some form of
// data structure that allows events to be dynamically scheduled, executed, and
// removed as the simulator advances through time." The Scheduler hosts the
// data structure; ScheduleEvent enters an Event into the calendar, Run drains
// each slot, and EventPool::Release recycles drained Events back into a
// free-list. Observing FreeCount() rise from 0 to N after Run() shows the full
// schedule→execute→remove cycle was applied to N scheduled events.
TEST(StratifiedEventSchedulerSim,
     SchedulerScheduledExecutedAndRemovedEventsThroughDataStructure) {
  Arena arena;
  Scheduler sched(arena);
  EXPECT_EQ(sched.GetEventPool().FreeCount(), 0u);

  int executed = 0;
  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&executed]() { ++executed; };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }
  EXPECT_TRUE(sched.HasEvents());

  sched.Run();
  EXPECT_EQ(executed, 5);
  EXPECT_FALSE(sched.HasEvents());
  EXPECT_EQ(sched.GetEventPool().FreeCount(), 5u);
}

// §4.4 ¶2: "Every event has one and only one simulation execution time, which
// at any given point during simulation can be the current time or some future
// time." ScheduleEvent takes a single SimTime, and the event must execute at
// exactly that time — once, not at any earlier or later slot.
TEST(StratifiedEventSchedulerSim, EventExecutesAtItsOneSimulationExecutionTime) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> fired_at;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { fired_at.push_back(sched.CurrentTime().ticks); };
  sched.ScheduleEvent({7}, Region::kActive, ev);

  sched.Run();
  ASSERT_EQ(fired_at.size(), 1u);
  EXPECT_EQ(fired_at[0], 7u);
}

// §4.4 ¶2: "...can be the current time or some future time." Both schedules
// are legal; current-time schedules execute within the in-progress slot's
// iteration, future-time schedules execute when the calendar advances.
TEST(StratifiedEventSchedulerSim, EventCanBeScheduledAtCurrentOrFutureTime) {
  Arena arena;
  Scheduler sched(arena);
  bool seeded_current = false;
  bool seeded_future = false;

  auto* seed = sched.GetEventPool().Acquire();
  seed->callback = [&]() {
    auto* now_event = sched.GetEventPool().Acquire();
    now_event->callback = [&]() { seeded_current = true; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kInactive, now_event);

    auto* future_event = sched.GetEventPool().Acquire();
    future_event->callback = [&]() { seeded_future = true; };
    sched.ScheduleEvent({sched.CurrentTime().ticks + 3}, Region::kActive,
                        future_event);
  };
  sched.ScheduleEvent({0}, Region::kActive, seed);

  sched.Run();
  EXPECT_TRUE(seeded_current);
  EXPECT_TRUE(seeded_future);
}

// §4.4 ¶2: "All scheduled events at a specific time define a time slot." Two
// events scheduled at the same SimTime must share one slot — both execute
// before CurrentTime advances past that time.
TEST(StratifiedEventSchedulerSim, EventsAtSameTimeShareASingleTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (int i = 0; i < 3; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { times.push_back(sched.CurrentTime().ticks); };
    sched.ScheduleEvent({4}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 4u);
  EXPECT_EQ(times[1], 4u);
  EXPECT_EQ(times[2], 4u);
}

// §4.4 ¶2: "Simulation proceeds by executing and removing all events in the
// current simulation time slot before moving on to the next nonempty time
// slot..." When events at time 0 and time 1 are both scheduled, every time-0
// event must complete (and be removed) before any time-1 event begins.
TEST(StratifiedEventSchedulerSim,
     CurrentTimeSlotFullyExecutedBeforeAdvancingToNext) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> sequence;

  auto* a0 = sched.GetEventPool().Acquire();
  a0->callback = [&]() { sequence.push_back(sched.CurrentTime().ticks); };
  sched.ScheduleEvent({0}, Region::kActive, a0);

  auto* nba0 = sched.GetEventPool().Acquire();
  nba0->callback = [&]() { sequence.push_back(sched.CurrentTime().ticks); };
  sched.ScheduleEvent({0}, Region::kNBA, nba0);

  auto* a1 = sched.GetEventPool().Acquire();
  a1->callback = [&]() { sequence.push_back(sched.CurrentTime().ticks); };
  sched.ScheduleEvent({1}, Region::kActive, a1);

  sched.Run();
  ASSERT_EQ(sequence.size(), 3u);
  EXPECT_EQ(sequence[0], 0u);
  EXPECT_EQ(sequence[1], 0u);
  EXPECT_EQ(sequence[2], 1u);
}

// §4.4 ¶2: "...moving on to the next nonempty time slot, in time order."
// Events scheduled at non-consecutive times must execute in ascending time
// order, skipping empty slots between them.
TEST(StratifiedEventSchedulerSim, NextNonemptyTimeSlotIsExecutedInTimeOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t : {17u, 3u, 99u, 0u}) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { times.push_back(sched.CurrentTime().ticks); };
    sched.ScheduleEvent({t}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 4u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 3u);
  EXPECT_EQ(times[2], 17u);
  EXPECT_EQ(times[3], 99u);
}

// §4.4 ¶3: "A time slot is divided into a set of ordered regions: a) Preponed,
// b) Pre-Active, c) Active, d) Inactive, e) Pre-NBA, f) NBA, g) Post-NBA,
// h) Pre-Observed, i) Observed, j) Post-Observed, k) Reactive, l) Re-Inactive,
// m) Pre-Re-NBA, n) Re-NBA, o) Post-Re-NBA, p) Pre-Postponed, q) Postponed."
// Seventeen regions, in that exact order. The Region enum and the Scheduler's
// per-slot drain order together encode the §4.4 ¶3 list — scheduling one event
// per region at the same time must produce execution in the listed order.
TEST(StratifiedEventSchedulerSim,
     TimeSlotIsDividedIntoSeventeenOrderedRegionsPerLrmList) {
  EXPECT_EQ(kRegionCount, 17u);

  Arena arena;
  Scheduler sched(arena);
  std::vector<Region> fired;

  std::vector<Region> all_regions = {
      Region::kPostponed,    Region::kPrePostponed, Region::kPostReNBA,
      Region::kReNBA,        Region::kPreReNBA,     Region::kReInactive,
      Region::kReactive,     Region::kPostObserved, Region::kObserved,
      Region::kPreObserved,  Region::kPostNBA,      Region::kNBA,
      Region::kPreNBA,       Region::kInactive,     Region::kActive,
      Region::kPreActive,    Region::kPreponed};
  for (Region r : all_regions) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&fired, r]() { fired.push_back(r); };
    sched.ScheduleEvent({0}, r, ev);
  }

  sched.Run();
  std::vector<Region> expected = {
      Region::kPreponed,     Region::kPreActive,    Region::kActive,
      Region::kInactive,     Region::kPreNBA,       Region::kNBA,
      Region::kPostNBA,      Region::kPreObserved,  Region::kObserved,
      Region::kPostObserved, Region::kReactive,     Region::kReInactive,
      Region::kPreReNBA,     Region::kReNBA,        Region::kPostReNBA,
      Region::kPrePostponed, Region::kPostponed};
  EXPECT_EQ(fired, expected);
}

// §4.4 ¶1 edge case: the rule says the data structure allows events to be
// scheduled, executed, and removed "as the simulator advances through time."
// The single-slot test above shows the cycle within one time slot; this test
// shows the same schedule→execute→release cycle holds when the calendar spans
// multiple time slots and CurrentTime advances between them.
TEST(StratifiedEventSchedulerSim,
     ScheduleExecuteRemoveCycleWorksAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  EXPECT_EQ(sched.GetEventPool().FreeCount(), 0u);

  int executed = 0;
  for (uint64_t t : {0u, 5u, 12u, 30u}) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&executed]() { ++executed; };
    sched.ScheduleEvent({t}, Region::kActive, ev);
  }
  EXPECT_TRUE(sched.HasEvents());

  sched.Run();
  EXPECT_EQ(executed, 4);
  EXPECT_FALSE(sched.HasEvents());
  EXPECT_EQ(sched.GetEventPool().FreeCount(), 4u);
  EXPECT_EQ(sched.CurrentTime().ticks, 30u);
}

// §4.4 ¶2 error condition: "This procedure guarantees that the simulator never
// goes backwards in time." Scheduler::ScheduleEvent enforces the guarantee by
// aborting whenever a caller hands it a SimTime less than CurrentTime.
// Without that defensive abort, a callback running inside a future slot could
// inject an event into a past slot and silently violate the no-backwards
// guarantee, so observing the abort fires is what shows the production code
// applies the §4.4 ¶2 guarantee. Death-test suite suffix per gtest convention.
TEST(StratifiedEventSchedulerSimDeathTest,
     SchedulingAtPastTimeAbortsToPreventBackwardsInTime) {
  EXPECT_DEATH(
      {
        Arena arena;
        Scheduler sched(arena);
        auto* future = sched.GetEventPool().Acquire();
        future->callback = [&]() {
          auto* past = sched.GetEventPool().Acquire();
          past->callback = []() {};
          sched.ScheduleEvent({50}, Region::kActive, past);
        };
        sched.ScheduleEvent({100}, Region::kActive, future);
        sched.Run();
      },
      "backwards-in-time");
}
