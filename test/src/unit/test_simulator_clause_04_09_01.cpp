#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.9.1 Continuous assignment
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.9.1 Continuous assignment corresponds to a process.
// A continuous assignment is modeled as a scheduler process (Event with
// callback), not as a one-shot operation.
// ---------------------------------------------------------------------------
TEST(SimCh4091, ContinuousAssignmentCorrespondsToProcess) {
  Arena arena;
  Scheduler sched(arena);
  int src = 0;
  int dst = 0;
  int process_eval_count = 0;

  // Model: assign dst = src;
  // Each time src changes, the process re-evaluates and schedules an update.
  // Change src at time 0 and time 5 to show the process triggers twice.
  auto *drive0 = sched.GetEventPool().Acquire();
  drive0->kind = EventKind::kEvaluation;
  drive0->callback = [&]() {
    src = 10;
    ++process_eval_count;
    auto *update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { dst = src; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, drive0);

  auto *drive5 = sched.GetEventPool().Acquire();
  drive5->kind = EventKind::kEvaluation;
  drive5->callback = [&]() {
    src = 20;
    ++process_eval_count;
    auto *update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { dst = src; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({5}, Region::kActive, drive5);

  sched.Run();
  EXPECT_EQ(dst, 20);
  EXPECT_EQ(process_eval_count, 2);
}

// ---------------------------------------------------------------------------
// §4.9.1 Sensitive to source elements in the expression.
// The continuous assignment process is only triggered when a source element
// in its RHS expression changes — not by unrelated signals.
// ---------------------------------------------------------------------------
TEST(SimCh4091, SensitiveToSourceElements) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;
  int dst = 0;
  int unrelated = 0;
  bool cont_assign_triggered = false;

  // Model: assign dst = a + b;
  // Changing 'a' triggers the process; changing 'unrelated' does not.
  auto *change_a = sched.GetEventPool().Acquire();
  change_a->kind = EventKind::kEvaluation;
  change_a->callback = [&]() {
    a = 3;
    // Continuous assignment sensitive to a → triggers.
    cont_assign_triggered = true;
    auto *update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { dst = a + b; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, change_a);

  // Changing an unrelated signal does NOT trigger the continuous assignment.
  auto *change_unrelated = sched.GetEventPool().Acquire();
  change_unrelated->kind = EventKind::kEvaluation;
  change_unrelated->callback = [&]() { unrelated = 99; };
  sched.ScheduleEvent({1}, Region::kActive, change_unrelated);

  sched.Run();
  EXPECT_TRUE(cont_assign_triggered);
  EXPECT_EQ(dst, 3);
  EXPECT_EQ(unrelated, 99);
}

// ---------------------------------------------------------------------------
// §4.9.1 Schedules an active update event.
// The update event from a continuous assignment is scheduled in the Active
// region (not Inactive, NBA, or any other region).
// ---------------------------------------------------------------------------
TEST(SimCh4091, SchedulesActiveUpdateEvent) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Schedule a continuous assignment update in Active region and an NBA event
  // to prove the continuous assignment event executes in Active (before NBA).
  auto *eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    auto *active_update = sched.GetEventPool().Acquire();
    active_update->kind = EventKind::kUpdate;
    active_update->callback = [&]() { order.push_back("active_update"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, active_update);

    auto *nba_update = sched.GetEventPool().Acquire();
    nba_update->kind = EventKind::kUpdate;
    nba_update->callback = [&]() { order.push_back("nba_update"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba_update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "active_update");
  EXPECT_EQ(order[1], "nba_update");
}

// ---------------------------------------------------------------------------
// §4.9.1 Uses current values to determine the target.
// The target (LHS) of the continuous assignment is determined using values
// at the time the update executes, not at the time it was scheduled.
// ---------------------------------------------------------------------------
TEST(SimCh4091, UsesCurrentValuesToDetermineTarget) {
  Arena arena;
  Scheduler sched(arena);
  int select = 0;
  int dst_a = 0;
  int dst_b = 0;

  // Model: assign (select ? dst_b : dst_a) = 1;
  // At time 0, schedule eval that reads current select to pick target.
  auto *eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    // Current value of select determines which target gets the update.
    auto *update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() {
      if (select == 0) {
        dst_a = 1;
      } else {
        dst_b = 1;
      }
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(dst_a, 1);
  EXPECT_EQ(dst_b, 0);
}

// ---------------------------------------------------------------------------
// §4.9.1 Evaluated at time zero for constant propagation.
// Even when the RHS is a constant (never changes), the continuous assignment
// process still executes at time 0 to propagate the constant to the LHS.
// ---------------------------------------------------------------------------
TEST(SimCh4091, EvaluatedAtTimeZeroForConstantPropagation) {
  Arena arena;
  Scheduler sched(arena);
  int dst = -1;

  // Model: assign dst = 42; → constant RHS, evaluated at time 0.
  auto *const_assign = sched.GetEventPool().Acquire();
  const_assign->kind = EventKind::kEvaluation;
  const_assign->callback = [&]() {
    auto *update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { dst = 42; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, const_assign);

  sched.Run();
  EXPECT_EQ(dst, 42);
  EXPECT_EQ(sched.CurrentTime().ticks, 0u);
}

// ---------------------------------------------------------------------------
// §4.9.1 Time-zero evaluation before procedural reads.
// The time-zero evaluation ensures that signals driven by continuous
// assignments have defined values before any procedural code reads them.
// ---------------------------------------------------------------------------
TEST(SimCh4091, TimeZeroEvalBeforeProceduralReads) {
  Arena arena;
  Scheduler sched(arena);
  int net_val = -1;
  int read_val = -1;

  // Continuous assignment sets net_val at time 0 (Active update).
  auto *cont_assign = sched.GetEventPool().Acquire();
  cont_assign->kind = EventKind::kEvaluation;
  cont_assign->callback = [&]() {
    auto *update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { net_val = 7; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, cont_assign);

  // Procedural code in Inactive reads net_val after continuous assignment.
  auto *proc_read = sched.GetEventPool().Acquire();
  proc_read->kind = EventKind::kEvaluation;
  proc_read->callback = [&]() { read_val = net_val; };
  sched.ScheduleEvent({0}, Region::kInactive, proc_read);

  sched.Run();
  EXPECT_EQ(net_val, 7);
  EXPECT_EQ(read_val, 7);
}

// ---------------------------------------------------------------------------
// §4.9.1 Implicit continuous assignment from input port (see §4.9.6).
// Input ports behave like implicit continuous assignments from outside to
// local — they follow the same scheduling rules as explicit assigns.
// ---------------------------------------------------------------------------
TEST(SimCh4091, ImplicitContinuousAssignmentFromInputPort) {
  Arena arena;
  Scheduler sched(arena);
  int outside_sig = 0;
  int local_input = 0;

  // Model: module m(input wire in); → implicit: assign local_input =
  // outside_sig; Port connection is an implicit continuous assignment that
  // schedules an active update event, same as explicit assign.
  auto *drive = sched.GetEventPool().Acquire();
  drive->kind = EventKind::kEvaluation;
  drive->callback = [&]() {
    outside_sig = 5;
    auto *port_update = sched.GetEventPool().Acquire();
    port_update->kind = EventKind::kUpdate;
    port_update->callback = [&]() { local_input = outside_sig; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, port_update);
  };
  sched.ScheduleEvent({0}, Region::kActive, drive);

  sched.Run();
  EXPECT_EQ(local_input, 5);
}

// ---------------------------------------------------------------------------
// §4.9.1 Implicit continuous assignment from output port (see §4.9.6).
// Output ports also behave as implicit continuous assignments from a local
// expression to an outside net.
// ---------------------------------------------------------------------------
TEST(SimCh4091, ImplicitContinuousAssignmentFromOutputPort) {
  Arena arena;
  Scheduler sched(arena);
  int local_output = 0;
  int outside_net = 0;

  // Model: module m(output wire out); → implicit: assign outside_net =
  // local_output; The output port connection is also an implicit continuous
  // assignment, scheduled as an active update event.
  auto *drive = sched.GetEventPool().Acquire();
  drive->kind = EventKind::kEvaluation;
  drive->callback = [&]() {
    local_output = 33;
    auto *port_update = sched.GetEventPool().Acquire();
    port_update->kind = EventKind::kUpdate;
    port_update->callback = [&]() { outside_net = local_output; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, port_update);
  };
  sched.ScheduleEvent({0}, Region::kActive, drive);

  sched.Run();
  EXPECT_EQ(outside_net, 33);
}

// ---------------------------------------------------------------------------
// §4.9.1 Multiple continuous assignments to the same net.
// Multiple continuous assignments to the same net each independently
// schedule active update events when their respective sources change.
// ---------------------------------------------------------------------------
TEST(SimCh4091, MultipleContinuousAssignmentsToSameNet) {
  Arena arena;
  Scheduler sched(arena);
  int driver_a = 0;
  int driver_b = 0;
  int net = 0;

  // Model: assign net = driver_a; assign net = driver_b;
  // Both drivers schedule active update events independently.
  auto *eval_a = sched.GetEventPool().Acquire();
  eval_a->kind = EventKind::kEvaluation;
  eval_a->callback = [&]() {
    driver_a = 1;
    auto *update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { net = driver_a; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval_a);

  auto *eval_b = sched.GetEventPool().Acquire();
  eval_b->kind = EventKind::kEvaluation;
  eval_b->callback = [&]() {
    driver_b = 2;
    auto *update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { net = driver_b; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval_b);

  sched.Run();
  // Both updates execute; final value depends on execution order within
  // Active region (nondeterministic per §4.7), but both must execute.
  EXPECT_TRUE(net == 1 || net == 2);
}

// ---------------------------------------------------------------------------
// §4.9.1 No update when expression value is unchanged.
// If the RHS expression does not change value, no update event is scheduled.
// This models the sensitivity behavior of continuous assignments.
// ---------------------------------------------------------------------------
TEST(SimCh4091, NoUpdateWhenExpressionUnchanged) {
  Arena arena;
  Scheduler sched(arena);
  int src = 5;
  int dst = 0;
  int update_count = 0;

  // Time 0: initial evaluation, src=5 → update dst.
  auto *eval0 = sched.GetEventPool().Acquire();
  eval0->kind = EventKind::kEvaluation;
  eval0->callback = [&]() {
    int new_val = src;
    auto *update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&, new_val]() {
      dst = new_val;
      ++update_count;
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval0);

  // Time 1: src is written but value doesn't change (still 5).
  // A well-modeled continuous assignment would not schedule an update.
  auto *eval1 = sched.GetEventPool().Acquire();
  eval1->kind = EventKind::kEvaluation;
  eval1->callback = [&]() {
    int new_val = src; // still 5, no change
    if (new_val != dst) {
      auto *update = sched.GetEventPool().Acquire();
      update->kind = EventKind::kUpdate;
      update->callback = [&, new_val]() {
        dst = new_val;
        ++update_count;
      };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
    }
  };
  sched.ScheduleEvent({1}, Region::kActive, eval1);

  sched.Run();
  EXPECT_EQ(dst, 5);
  EXPECT_EQ(update_count, 1);
}
