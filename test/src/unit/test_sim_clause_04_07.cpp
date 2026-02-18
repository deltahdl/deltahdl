#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.7 Nondeterminism
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.7 Active region events processed in any order.
// Multiple independent events in the Active region all execute within the
// same time slot — the scheduler must process them all.
// ---------------------------------------------------------------------------
TEST(SimCh47, ActiveRegionProcessesAllEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

// ---------------------------------------------------------------------------
// §4.7 Reactive region events processed in any order.
// Multiple independent events in the Reactive region all execute within the
// same time slot.
// ---------------------------------------------------------------------------
TEST(SimCh47, ReactiveRegionProcessesAllEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kReactive, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

// ---------------------------------------------------------------------------
// §4.7 Independent Active processes can interleave.
// Two independent processes each schedule events in Active; both see each
// other's results regardless of execution order.
// ---------------------------------------------------------------------------
TEST(SimCh47, IndependentActiveProcessesInterleave) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;

  // Process A writes a.
  auto* ev_a = sched.GetEventPool().Acquire();
  ev_a->callback = [&]() { a = 1; };
  sched.ScheduleEvent({0}, Region::kActive, ev_a);

  // Process B writes b.
  auto* ev_b = sched.GetEventPool().Acquire();
  ev_b->callback = [&]() { b = 2; };
  sched.ScheduleEvent({0}, Region::kActive, ev_b);

  sched.Run();
  // Both processes executed — regardless of order, both values are set.
  EXPECT_EQ(a, 1);
  EXPECT_EQ(b, 2);
}

// ---------------------------------------------------------------------------
// §4.7 Independent Reactive processes interleave.
// Two independent processes in Reactive region; both execute.
// ---------------------------------------------------------------------------
TEST(SimCh47, IndependentReactiveProcessesInterleave) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;

  auto* ev_a = sched.GetEventPool().Acquire();
  ev_a->callback = [&]() { a = 10; };
  sched.ScheduleEvent({0}, Region::kReactive, ev_a);

  auto* ev_b = sched.GetEventPool().Acquire();
  ev_b->callback = [&]() { b = 20; };
  sched.ScheduleEvent({0}, Region::kReactive, ev_b);

  sched.Run();
  EXPECT_EQ(a, 10);
  EXPECT_EQ(b, 20);
}

// ---------------------------------------------------------------------------
// §4.7 Process suspension and pending event placement.
// A process suspends via #0 (Inactive region) and resumes later. This models
// process suspension without time-control — the scheduler places the
// continuation as a pending event.
// ---------------------------------------------------------------------------
TEST(SimCh47, ProcessSuspensionViaPendingEvent) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Process A: executes part 1, suspends (schedules continuation in Inactive).
  auto* a_part1 = sched.GetEventPool().Acquire();
  a_part1->callback = [&]() {
    order.push_back("A_part1");
    auto* a_part2 = sched.GetEventPool().Acquire();
    a_part2->callback = [&]() { order.push_back("A_part2"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kInactive, a_part2);
  };
  sched.ScheduleEvent({0}, Region::kActive, a_part1);

  // Process B: runs during A's suspension.
  auto* b = sched.GetEventPool().Acquire();
  b->callback = [&]() { order.push_back("B"); };
  sched.ScheduleEvent({0}, Region::kActive, b);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "A_part1");
  EXPECT_EQ(order[1], "B");
  // A resumes after Inactive → Active iteration.
  EXPECT_EQ(order[2], "A_part2");
}

// ---------------------------------------------------------------------------
// §4.7 Process execution interleaving.
// Multiple processes interleave through suspension. Process A and C both
// suspend, allowing B to run in between.
// ---------------------------------------------------------------------------
TEST(SimCh47, MultipleProcessInterleaving) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Process A: part1 in Active, part2 in Inactive.
  auto* a1 = sched.GetEventPool().Acquire();
  a1->callback = [&]() {
    order.push_back("A1");
    auto* a2 = sched.GetEventPool().Acquire();
    a2->callback = [&]() { order.push_back("A2"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kInactive, a2);
  };
  sched.ScheduleEvent({0}, Region::kActive, a1);

  // Process B: runs in Active without suspension.
  auto* b = sched.GetEventPool().Acquire();
  b->callback = [&]() { order.push_back("B"); };
  sched.ScheduleEvent({0}, Region::kActive, b);

  // Process C: part1 in Active, part2 in Inactive.
  auto* c1 = sched.GetEventPool().Acquire();
  c1->callback = [&]() {
    order.push_back("C1");
    auto* c2 = sched.GetEventPool().Acquire();
    c2->callback = [&]() { order.push_back("C2"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kInactive, c2);
  };
  sched.ScheduleEvent({0}, Region::kActive, c1);

  sched.Run();
  ASSERT_EQ(order.size(), 5u);
  // Active phase: A1, B, C1 (all Active events drain first).
  EXPECT_EQ(order[0], "A1");
  EXPECT_EQ(order[1], "B");
  EXPECT_EQ(order[2], "C1");
  // Inactive→Active iteration: A2, C2 (suspended processes resume).
  EXPECT_EQ(order[3], "A2");
  EXPECT_EQ(order[4], "C2");
}

// ---------------------------------------------------------------------------
// §4.7 Nondeterministic interleaved execution order.
// The scheduler processes events from a region but the result (cumulative
// side effects) reflects all events having executed. With conflicting writes,
// the last-executed wins — the user cannot control which wins.
// ---------------------------------------------------------------------------
TEST(SimCh47, ConflictingWritesInActiveRegion) {
  Arena arena;
  Scheduler sched(arena);
  int x = 0;

  // Two processes both write to x — the final value depends on execution
  // order. We verify both writes execute (x is set by one of them).
  auto* ev1 = sched.GetEventPool().Acquire();
  ev1->callback = [&]() { x = 10; };
  sched.ScheduleEvent({0}, Region::kActive, ev1);

  auto* ev2 = sched.GetEventPool().Acquire();
  ev2->callback = [&]() { x = 20; };
  sched.ScheduleEvent({0}, Region::kActive, ev2);

  sched.Run();
  // In our FIFO implementation, the last-scheduled event wins.
  // The LRM says either value is valid — we just verify one of them holds.
  EXPECT_TRUE(x == 10 || x == 20);
}

// ---------------------------------------------------------------------------
// §4.7 Dynamically generated Active events execute in same time slot.
// An Active callback that generates new Active events — the dynamically
// generated events also execute within the same time slot iteration.
// ---------------------------------------------------------------------------
TEST(SimCh47, DynamicallyGeneratedActiveEventsExecute) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  // An Active callback generates three more Active events.
  auto* gen = sched.GetEventPool().Acquire();
  gen->callback = [&]() {
    order.push_back(0);
    for (int i = 1; i <= 3; ++i) {
      auto* ev = sched.GetEventPool().Acquire();
      ev->callback = [&order, i]() { order.push_back(i); };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, ev);
    }
  };
  sched.ScheduleEvent({0}, Region::kActive, gen);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], 0);
  // All generated events execute (order among them is implementation-defined).
  EXPECT_EQ(order[1], 1);
  EXPECT_EQ(order[2], 2);
  EXPECT_EQ(order[3], 3);
}

// ---------------------------------------------------------------------------
// §4.7 Reactive region suspension via Re-Inactive.
// A Reactive process suspends via Re-Inactive and resumes, allowing other
// Reactive processes to interleave.
// ---------------------------------------------------------------------------
TEST(SimCh47, ReactiveProcessSuspensionViaReInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Reactive process A: suspends via Re-Inactive.
  auto* a1 = sched.GetEventPool().Acquire();
  a1->callback = [&]() {
    order.push_back("RA1");
    auto* a2 = sched.GetEventPool().Acquire();
    a2->callback = [&]() { order.push_back("RA2"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kReInactive, a2);
  };
  sched.ScheduleEvent({0}, Region::kReactive, a1);

  // Reactive process B.
  auto* b = sched.GetEventPool().Acquire();
  b->callback = [&]() { order.push_back("RB"); };
  sched.ScheduleEvent({0}, Region::kReactive, b);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "RA1");
  EXPECT_EQ(order[1], "RB");
  // A resumes after Re-Inactive → Reactive iteration.
  EXPECT_EQ(order[2], "RA2");
}

// ---------------------------------------------------------------------------
// §4.7 Nondeterminism across multiple time slots.
// Each time slot independently has nondeterministic ordering among its events.
// Both time slots execute all their events.
// ---------------------------------------------------------------------------
TEST(SimCh47, NondeterminismAcrossTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Time 0: two independent processes.
  auto* t0a = sched.GetEventPool().Acquire();
  t0a->callback = [&]() { order.push_back("t0_a"); };
  sched.ScheduleEvent({0}, Region::kActive, t0a);

  auto* t0b = sched.GetEventPool().Acquire();
  t0b->callback = [&]() { order.push_back("t0_b"); };
  sched.ScheduleEvent({0}, Region::kActive, t0b);

  // Time 5: two independent processes.
  auto* t5a = sched.GetEventPool().Acquire();
  t5a->callback = [&]() { order.push_back("t5_a"); };
  sched.ScheduleEvent({5}, Region::kActive, t5a);

  auto* t5b = sched.GetEventPool().Acquire();
  t5b->callback = [&]() { order.push_back("t5_b"); };
  sched.ScheduleEvent({5}, Region::kActive, t5b);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  // Time 0 events both execute before time 5 (deterministic time ordering).
  // Within each time slot, both events execute (order is nondeterministic).
  // Verify both t0 events are present.
  std::vector<std::string> t0(order.begin(), order.begin() + 2);
  std::sort(t0.begin(), t0.end());
  EXPECT_EQ(t0, (std::vector<std::string>{"t0_a", "t0_b"}));
  // Verify both t5 events are present.
  std::vector<std::string> t5(order.begin() + 2, order.end());
  std::sort(t5.begin(), t5.end());
  EXPECT_EQ(t5, (std::vector<std::string>{"t5_a", "t5_b"}));
}
