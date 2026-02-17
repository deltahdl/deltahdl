#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.8 Race conditions
//
// LRM §4.8:
//   "Because the execution of expression evaluation and net update events may
//    be intermingled, race conditions are possible."
//
//   Example:
//     assign p = q;
//     initial begin
//       q = 1;
//       #1 q = 0;
//       $display(p);
//     end
//
//   "The simulator is correct in displaying either a 1 or a 0. The assignment
//    of 0 to q enables an update event for p. The simulator may either
//    continue and execute the $display task or execute the update for p,
//    followed by the $display task."
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.8 "the execution of expression evaluation and net update events may be
// intermingled"
// Both kEvaluation and kUpdate events in the Active region execute — the
// scheduler interleaves them.
// ---------------------------------------------------------------------------
TEST(SimCh48, EvalAndUpdateEventsIntermingleInActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // An evaluation event.
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() { order.push_back("eval"); };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  // An update event.
  auto* update = sched.GetEventPool().Acquire();
  update->kind = EventKind::kUpdate;
  update->callback = [&]() { order.push_back("update"); };
  sched.ScheduleEvent({0}, Region::kActive, update);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  // Both events executed — order depends on implementation (FIFO here).
  EXPECT_TRUE((order[0] == "eval" && order[1] == "update") ||
              (order[0] == "update" && order[1] == "eval"));
}

// ---------------------------------------------------------------------------
// §4.8 "The assignment of 0 to q enables an update event for p"
// A blocking assignment that modifies a variable triggers an update event
// (continuous assignment). Both the process continuation and the update event
// are in the Active region.
// ---------------------------------------------------------------------------
TEST(SimCh48, BlockingAssignmentTriggersUpdateEvent) {
  Arena arena;
  Scheduler sched(arena);
  int q = 1;
  int p = 1;

  // Simulate: at time 1, q = 0 (blocking assignment).
  // This triggers an update event for p (continuous assignment: assign p = q).
  auto* assign_q = sched.GetEventPool().Acquire();
  assign_q->kind = EventKind::kEvaluation;
  assign_q->callback = [&]() {
    q = 0;
    // The continuous assignment "assign p = q" triggers an update event.
    auto* update_p = sched.GetEventPool().Acquire();
    update_p->kind = EventKind::kUpdate;
    update_p->callback = [&]() { p = q; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update_p);
  };
  sched.ScheduleEvent({1}, Region::kActive, assign_q);

  sched.Run();
  EXPECT_EQ(q, 0);
  EXPECT_EQ(p, 0);  // Update event executed, p reflects new q.
}

// ---------------------------------------------------------------------------
// §4.8 "The simulator may either continue and execute the $display task or
// execute the update for p"
// The update event and the process continuation (next statement) are both
// Active events — they race.
// ---------------------------------------------------------------------------
TEST(SimCh48, UpdateEventRacesWithProcessContinuation) {
  Arena arena;
  Scheduler sched(arena);
  int p = 1;
  int q = 1;
  int display_value = -1;

  // Process: q = 0 triggers update for p; $display(p) follows.
  auto* process = sched.GetEventPool().Acquire();
  process->kind = EventKind::kEvaluation;
  process->callback = [&]() {
    q = 0;
    // Schedule update event for p (from continuous assignment).
    auto* update_p = sched.GetEventPool().Acquire();
    update_p->kind = EventKind::kUpdate;
    update_p->callback = [&]() { p = q; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update_p);

    // Schedule process continuation ($display(p)).
    auto* display = sched.GetEventPool().Acquire();
    display->kind = EventKind::kEvaluation;
    display->callback = [&]() { display_value = p; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, display);
  };
  sched.ScheduleEvent({1}, Region::kActive, process);

  sched.Run();
  // Either value is valid per the LRM — depends on execution order.
  EXPECT_TRUE(display_value == 0 || display_value == 1);
}

// ---------------------------------------------------------------------------
// §4.8 "The simulator is correct in displaying either a 1 or a 0"
// Both race outcomes are valid. In our FIFO implementation, the update
// executes first (it was scheduled first), so display sees the updated value.
// ---------------------------------------------------------------------------
TEST(SimCh48, BothRaceOutcomesAreValid) {
  Arena arena;
  Scheduler sched(arena);
  int p = 1;
  std::vector<int> observed_p;

  // Two interleaved events: update p, then read p.
  auto* update_p = sched.GetEventPool().Acquire();
  update_p->kind = EventKind::kUpdate;
  update_p->callback = [&]() { p = 0; };
  sched.ScheduleEvent({1}, Region::kActive, update_p);

  auto* read_p = sched.GetEventPool().Acquire();
  read_p->kind = EventKind::kEvaluation;
  read_p->callback = [&]() { observed_p.push_back(p); };
  sched.ScheduleEvent({1}, Region::kActive, read_p);

  sched.Run();
  ASSERT_EQ(observed_p.size(), 1u);
  // LRM says either old (1) or new (0) is correct.
  EXPECT_TRUE(observed_p[0] == 0 || observed_p[0] == 1);
}

// ---------------------------------------------------------------------------
// §4.8 LRM example: "assign p = q; initial begin q = 1; #1 q = 0;
// $display(p); end"
// Full simulation of the LRM example across two time slots.
// ---------------------------------------------------------------------------
TEST(SimCh48, LRMExampleAssignPEqualsQ) {
  Arena arena;
  Scheduler sched(arena);
  int q = 0;
  int p = 0;
  int display_result = -1;

  // Time 0: q = 1 (initial block starts).
  auto* init_q = sched.GetEventPool().Acquire();
  init_q->kind = EventKind::kEvaluation;
  init_q->callback = [&]() {
    q = 1;
    // Continuous assignment updates p.
    auto* update_p = sched.GetEventPool().Acquire();
    update_p->kind = EventKind::kUpdate;
    update_p->callback = [&]() { p = q; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update_p);
  };
  sched.ScheduleEvent({0}, Region::kActive, init_q);

  // Time 1: q = 0 and $display(p) — these race.
  auto* assign_zero = sched.GetEventPool().Acquire();
  assign_zero->kind = EventKind::kEvaluation;
  assign_zero->callback = [&]() {
    q = 0;
    // Continuous assignment: assign p = q → schedule update.
    auto* update_p = sched.GetEventPool().Acquire();
    update_p->kind = EventKind::kUpdate;
    update_p->callback = [&]() { p = q; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update_p);

    // $display(p) — races with the update.
    auto* display = sched.GetEventPool().Acquire();
    display->kind = EventKind::kEvaluation;
    display->callback = [&]() { display_result = p; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, display);
  };
  sched.ScheduleEvent({1}, Region::kActive, assign_zero);

  sched.Run();
  // At time 0: p should be 1 (q was set to 1, update propagated).
  // At time 1: display_result is either 0 or 1 — both valid per LRM.
  EXPECT_TRUE(display_result == 0 || display_result == 1);
}

// ---------------------------------------------------------------------------
// §4.8 "expression evaluation and net update events may be intermingled"
// Multiple update events from different continuous assignments all race
// with each other and with evaluation events.
// ---------------------------------------------------------------------------
TEST(SimCh48, MultipleUpdateEventsRaceWithEachOther) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;
  int c = 0;

  // Three update events from different continuous assignments, all Active.
  auto* u1 = sched.GetEventPool().Acquire();
  u1->kind = EventKind::kUpdate;
  u1->callback = [&]() { a = 1; };
  sched.ScheduleEvent({0}, Region::kActive, u1);

  auto* u2 = sched.GetEventPool().Acquire();
  u2->kind = EventKind::kUpdate;
  u2->callback = [&]() { b = 2; };
  sched.ScheduleEvent({0}, Region::kActive, u2);

  auto* u3 = sched.GetEventPool().Acquire();
  u3->kind = EventKind::kUpdate;
  u3->callback = [&]() { c = 3; };
  sched.ScheduleEvent({0}, Region::kActive, u3);

  sched.Run();
  // All updates execute (order among them is nondeterministic per LRM).
  EXPECT_EQ(a, 1);
  EXPECT_EQ(b, 2);
  EXPECT_EQ(c, 3);
}

// ---------------------------------------------------------------------------
// §4.8 "expression evaluation and net update events may be intermingled"
// A process writes to multiple variables with continuous assignments,
// generating multiple racing update events.
// ---------------------------------------------------------------------------
TEST(SimCh48, RaceConditionAcrossMultipleNets) {
  Arena arena;
  Scheduler sched(arena);
  int x = 0;
  int y = 0;
  int net_x = 0;
  int net_y = 0;
  int observed_net_x = -1;
  int observed_net_y = -1;

  // Process: x = 10; y = 20; → triggers updates for net_x and net_y.
  auto* process = sched.GetEventPool().Acquire();
  process->kind = EventKind::kEvaluation;
  process->callback = [&]() {
    x = 10;
    y = 20;

    auto* ux = sched.GetEventPool().Acquire();
    ux->kind = EventKind::kUpdate;
    ux->callback = [&]() { net_x = x; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, ux);

    auto* uy = sched.GetEventPool().Acquire();
    uy->kind = EventKind::kUpdate;
    uy->callback = [&]() { net_y = y; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, uy);

    // Observe values — races with the updates.
    auto* observe = sched.GetEventPool().Acquire();
    observe->kind = EventKind::kEvaluation;
    observe->callback = [&]() {
      observed_net_x = net_x;
      observed_net_y = net_y;
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, observe);
  };
  sched.ScheduleEvent({0}, Region::kActive, process);

  sched.Run();
  // Both nets ultimately have correct values.
  EXPECT_EQ(net_x, 10);
  EXPECT_EQ(net_y, 20);
  // Observed values depend on race — either old or new is valid.
  EXPECT_TRUE(observed_net_x == 0 || observed_net_x == 10);
  EXPECT_TRUE(observed_net_y == 0 || observed_net_y == 20);
}

// ---------------------------------------------------------------------------
// §4.8 "expression evaluation and net update events may be intermingled"
// Both kEvaluation and kUpdate EventKind tags are distinct, and both
// execute in the Active region — the scheduler dispatches both.
// ---------------------------------------------------------------------------
TEST(SimCh48, EvalAndUpdateEventKindsDistinct) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<EventKind> kinds;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() { kinds.push_back(EventKind::kEvaluation); };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  auto* update = sched.GetEventPool().Acquire();
  update->kind = EventKind::kUpdate;
  update->callback = [&]() { kinds.push_back(EventKind::kUpdate); };
  sched.ScheduleEvent({0}, Region::kActive, update);

  sched.Run();
  ASSERT_EQ(kinds.size(), 2u);
  // Both kinds executed; they are distinct enum values.
  EXPECT_NE(EventKind::kEvaluation, EventKind::kUpdate);
  EXPECT_EQ(kinds[0], EventKind::kEvaluation);
  EXPECT_EQ(kinds[1], EventKind::kUpdate);
}

// ---------------------------------------------------------------------------
// §4.8 Race conditions only arise when events are in the SAME region.
// Events in different regions have deterministic ordering (§4.5) — no race.
// ---------------------------------------------------------------------------
TEST(SimCh48, NoRaceBetweenDifferentRegions) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int observed = -1;

  // Active region: set value.
  auto* active = sched.GetEventPool().Acquire();
  active->kind = EventKind::kUpdate;
  active->callback = [&]() { value = 42; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  // NBA region: read value — deterministically after Active.
  auto* nba = sched.GetEventPool().Acquire();
  nba->kind = EventKind::kEvaluation;
  nba->callback = [&]() { observed = value; };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  sched.Run();
  // No race: NBA always executes after Active (§4.5 region ordering).
  EXPECT_EQ(observed, 42);
}

// ---------------------------------------------------------------------------
// §4.8 "expression evaluation and net update events may be intermingled"
// NBAs avoid the race: using nonblocking assignments (NBA region) ensures
// updates happen in a separate phase, eliminating the Active-region race.
// ---------------------------------------------------------------------------
TEST(SimCh48, NBAEliminatesActiveRegionRace) {
  Arena arena;
  Scheduler sched(arena);
  int q = 1;
  int p = 1;
  int display_value = -1;

  // Process in Active: q <= 0 (NBA), then $display(p).
  auto* process = sched.GetEventPool().Acquire();
  process->kind = EventKind::kEvaluation;
  process->callback = [&]() {
    // Schedule NBA for q.
    auto* nba_q = sched.GetEventPool().Acquire();
    nba_q->kind = EventKind::kUpdate;
    nba_q->callback = [&]() {
      q = 0;
      // Continuous assignment: schedule update for p in Active (next
      // iteration).
      auto* update_p = sched.GetEventPool().Acquire();
      update_p->kind = EventKind::kUpdate;
      update_p->callback = [&]() { p = q; };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update_p);
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba_q);

    // $display(p) in Active — runs before NBA region.
    display_value = p;
  };
  sched.ScheduleEvent({0}, Region::kActive, process);

  sched.Run();
  // $display(p) in Active sees old value of p (1), because NBA hasn't
  // fired yet. No race — deterministic ordering.
  EXPECT_EQ(display_value, 1);
  // After NBA + re-iteration, p is updated.
  EXPECT_EQ(p, 0);
}
