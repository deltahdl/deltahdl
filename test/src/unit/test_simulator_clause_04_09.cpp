#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.9 Scheduling implication of assignments
//
// Every assignment type in SystemVerilog is implemented through the
// scheduler's process/event model. The seven assignment types are:
//   4.9.1 Continuous assignment
//   4.9.2 Procedural continuous assignment
//   4.9.3 Blocking assignment
//   4.9.4 Nonblocking assignment
//   4.9.5 Switch (transistor) processing
//   4.9.6 Port connections
//   4.9.7 Subroutines
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.9 Continuous assignment (4.9.1) as process and event.
// A process sensitive to source elements schedules an active update event
// when the expression changes.
// ---------------------------------------------------------------------------
TEST(SimCh49, ContinuousAssignmentAsProcessAndEvent) {
  Arena arena;
  Scheduler sched(arena);
  int src = 0;
  int dst = 0;

  // Model: assign dst = src; → process triggers update event when src changes.
  // Time 0: src changes to 5 → schedules active update for dst.
  auto* process = sched.GetEventPool().Acquire();
  process->kind = EventKind::kEvaluation;
  process->callback = [&]() {
    src = 5;
    // Continuous assignment triggers an active update event.
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { dst = src; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, process);

  sched.Run();
  EXPECT_EQ(dst, 5);
}

// ---------------------------------------------------------------------------
// §4.9 Procedural continuous assignment (4.9.2) as process and event.
// assign/force creates a process sensitive to the expression;
// deassign/release deactivates it.
// ---------------------------------------------------------------------------
TEST(SimCh49, ProceduralContinuousAssignmentAsProcessAndEvent) {
  Arena arena;
  Scheduler sched(arena);
  int forced_val = 0;
  bool force_active = true;

  // Model: force dst = expr; → process schedules active update events.
  // A subsequent release deactivates the process.
  auto* force_proc = sched.GetEventPool().Acquire();
  force_proc->kind = EventKind::kEvaluation;
  force_proc->callback = [&]() {
    if (force_active) {
      auto* update = sched.GetEventPool().Acquire();
      update->kind = EventKind::kUpdate;
      update->callback = [&]() { forced_val = 42; };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
    }
  };
  sched.ScheduleEvent({0}, Region::kActive, force_proc);

  // Time 1: release → deactivate force, value stays.
  auto* release_proc = sched.GetEventPool().Acquire();
  release_proc->kind = EventKind::kEvaluation;
  release_proc->callback = [&]() { force_active = false; };
  sched.ScheduleEvent({1}, Region::kActive, release_proc);

  sched.Run();
  EXPECT_EQ(forced_val, 42);
  EXPECT_FALSE(force_active);
}

// ---------------------------------------------------------------------------
// §4.9 Blocking assignment (4.9.3) as process and event.
// With intra-assignment delay, the process suspends and is scheduled as
// a future event.
// ---------------------------------------------------------------------------
TEST(SimCh49, BlockingAssignmentAsProcessAndEvent) {
  Arena arena;
  Scheduler sched(arena);
  int result = 0;
  SimTime resume_time{0};

  // Model: result = #2 expr; → compute RHS, suspend, resume at time 2.
  auto* proc = sched.GetEventPool().Acquire();
  proc->kind = EventKind::kEvaluation;
  proc->callback = [&]() {
    int rhs = 99;  // Compute RHS with current values.
    // Suspend: schedule future event at current_time + 2.
    auto* resume = sched.GetEventPool().Acquire();
    resume->kind = EventKind::kEvaluation;
    resume->callback = [&, rhs]() {
      resume_time = sched.CurrentTime();
      result = rhs;
    };
    sched.ScheduleEvent({sched.CurrentTime().ticks + 2}, Region::kActive,
                        resume);
  };
  sched.ScheduleEvent({0}, Region::kActive, proc);

  sched.Run();
  EXPECT_EQ(result, 99);
  EXPECT_EQ(resume_time.ticks, 2u);
}

// ---------------------------------------------------------------------------
// §4.9 Blocking assignment with zero delay (4.9.3).
// Process is scheduled as an Inactive event for the current time.
// ---------------------------------------------------------------------------
TEST(SimCh49, BlockingAssignmentZeroDelaySchedulesInactive) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  std::vector<std::string> order;

  // Model: value = #0 expr; → schedules in Inactive (not Active).
  auto* proc = sched.GetEventPool().Acquire();
  proc->kind = EventKind::kEvaluation;
  proc->callback = [&]() {
    order.push_back("active");
    int rhs = 10;
    // #0 delay → schedule in Inactive region.
    auto* resume = sched.GetEventPool().Acquire();
    resume->kind = EventKind::kEvaluation;
    resume->callback = [&, rhs]() {
      order.push_back("inactive");
      value = rhs;
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kInactive, resume);
  };
  sched.ScheduleEvent({0}, Region::kActive, proc);

  sched.Run();
  EXPECT_EQ(value, 10);
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "inactive");
}

// ---------------------------------------------------------------------------
// §4.9 Nonblocking assignment (4.9.4) as NBA event.
// Always computes the updated value and schedules the update as an NBA
// update event.
// ---------------------------------------------------------------------------
TEST(SimCh49, NonblockingAssignmentAsNBAEvent) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;

  // Model: a <= 1; b <= 2; → NBA updates scheduled, execute after Active.
  auto* proc = sched.GetEventPool().Acquire();
  proc->kind = EventKind::kEvaluation;
  proc->callback = [&]() {
    int rhs_a = 1;
    int rhs_b = 2;
    auto* nba_a = sched.GetEventPool().Acquire();
    nba_a->kind = EventKind::kUpdate;
    nba_a->callback = [&, rhs_a]() { a = rhs_a; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba_a);

    auto* nba_b = sched.GetEventPool().Acquire();
    nba_b->kind = EventKind::kUpdate;
    nba_b->callback = [&, rhs_b]() { b = rhs_b; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba_b);
  };
  sched.ScheduleEvent({0}, Region::kActive, proc);

  sched.Run();
  EXPECT_EQ(a, 1);
  EXPECT_EQ(b, 2);
}

// ---------------------------------------------------------------------------
// §4.9 Switch processing (4.9.5) as active events.
// Bidirectional switch events are scheduled as active update events,
// intermingled with other active events.
// ---------------------------------------------------------------------------
TEST(SimCh49, SwitchProcessingAsActiveEvents) {
  Arena arena;
  Scheduler sched(arena);
  int node_a = 0;
  int node_b = 0;

  // Model: tran(a, b) — bidirectional switch propagates values as active
  // update events intermingled with other events.
  auto* drive = sched.GetEventPool().Acquire();
  drive->kind = EventKind::kEvaluation;
  drive->callback = [&]() { node_a = 1; };
  sched.ScheduleEvent({0}, Region::kActive, drive);

  auto* switch_prop = sched.GetEventPool().Acquire();
  switch_prop->kind = EventKind::kUpdate;
  switch_prop->callback = [&]() { node_b = node_a; };
  sched.ScheduleEvent({0}, Region::kActive, switch_prop);

  sched.Run();
  EXPECT_EQ(node_a, 1);
  EXPECT_EQ(node_b, 1);
}

// ---------------------------------------------------------------------------
// §4.9 Port connections (4.9.6) as implicit continuous assignments.
// Ports connect processes through implicit continuous assignment statements.
// ---------------------------------------------------------------------------
TEST(SimCh49, PortConnectionAsImplicitContinuousAssignment) {
  Arena arena;
  Scheduler sched(arena);
  int outside_sig = 0;
  int local_input = 0;

  // Model: input port — implicit continuous assignment from outside to local.
  auto* driver = sched.GetEventPool().Acquire();
  driver->kind = EventKind::kEvaluation;
  driver->callback = [&]() {
    outside_sig = 7;
    // Implicit continuous assignment: local_input = outside_sig.
    auto* port_update = sched.GetEventPool().Acquire();
    port_update->kind = EventKind::kUpdate;
    port_update->callback = [&]() { local_input = outside_sig; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, port_update);
  };
  sched.ScheduleEvent({0}, Region::kActive, driver);

  sched.Run();
  EXPECT_EQ(local_input, 7);
}

// ---------------------------------------------------------------------------
// §4.9 Subroutines (4.9.7) as blocking assignment events.
// Copy-in on invocation and copy-out on return behave as blocking
// assignments, modeled as evaluation events.
// ---------------------------------------------------------------------------
TEST(SimCh49, SubroutineArgumentPassingAsBlockingAssignment) {
  Arena arena;
  Scheduler sched(arena);
  int caller_arg = 10;
  int callee_local = 0;
  int caller_out = 0;

  // Model: task with output — copy-in at call, copy-out at return.
  auto* call = sched.GetEventPool().Acquire();
  call->kind = EventKind::kEvaluation;
  call->callback = [&]() {
    // Copy-in: callee gets a copy of caller_arg.
    callee_local = caller_arg;
    // Subroutine body modifies local copy.
    callee_local += 5;
    // Copy-out on return: behaves as blocking assignment.
    caller_out = callee_local;
  };
  sched.ScheduleEvent({0}, Region::kActive, call);

  sched.Run();
  EXPECT_EQ(caller_out, 15);
}

// ---------------------------------------------------------------------------
// §4.9 All seven assignment types use the same scheduler infrastructure.
// They all go through ScheduleEvent.
// ---------------------------------------------------------------------------
TEST(SimCh49, AllAssignmentTypesUseSchedulerInfrastructure) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> executed;

  // Schedule one event per assignment type to show they all use the same
  // scheduler infrastructure (ScheduleEvent → Region → EventQueue → Run).
  auto schedule = [&](const std::string& label, Region region) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->kind = EventKind::kUpdate;
    ev->callback = [&executed, label]() { executed.push_back(label); };
    sched.ScheduleEvent({0}, region, ev);
  };

  schedule("continuous", Region::kActive);       // §4.9.1
  schedule("proc_continuous", Region::kActive);  // §4.9.2
  schedule("blocking", Region::kInactive);       // §4.9.3 (zero delay)
  schedule("nonblocking", Region::kNBA);         // §4.9.4
  schedule("switch", Region::kActive);           // §4.9.5
  schedule("port", Region::kActive);             // §4.9.6
  schedule("subroutine", Region::kActive);       // §4.9.7

  sched.Run();
  EXPECT_EQ(executed.size(), 7u);
}

// ---------------------------------------------------------------------------
// §4.9 Assignment ordering follows region ordering (§4.5).
// Active → Inactive → NBA.
// ---------------------------------------------------------------------------
TEST(SimCh49, AssignmentOrderingFollowsRegionOrdering) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Continuous assignment → Active update event.
  auto* cont = sched.GetEventPool().Acquire();
  cont->kind = EventKind::kUpdate;
  cont->callback = [&]() { order.push_back("continuous_active"); };
  sched.ScheduleEvent({0}, Region::kActive, cont);

  // Blocking assignment #0 → Inactive event.
  auto* blk = sched.GetEventPool().Acquire();
  blk->kind = EventKind::kEvaluation;
  blk->callback = [&]() { order.push_back("blocking_inactive"); };
  sched.ScheduleEvent({0}, Region::kInactive, blk);

  // Nonblocking assignment → NBA event.
  auto* nba = sched.GetEventPool().Acquire();
  nba->kind = EventKind::kUpdate;
  nba->callback = [&]() { order.push_back("nba"); };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "continuous_active");
  EXPECT_EQ(order[1], "blocking_inactive");
  EXPECT_EQ(order[2], "nba");
}
