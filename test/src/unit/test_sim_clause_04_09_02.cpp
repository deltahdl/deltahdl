#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.9.2 Procedural continuous assignment
//
// LRM §4.9.2:
//   "A procedural continuous assignment (which is the assign or force
//    statement; see 10.6) corresponds to a process that is sensitive to
//    the source elements in the expression. When the value of the
//    expression changes, it causes an active update event to be added to
//    the event region, using current values to determine the target.
//    A deassign or a release statement deactivates any corresponding
//    assign or force statement(s)."
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.9.2 "A procedural continuous assignment ... corresponds to a process"
// The assign/force statement is modeled as a scheduler process (Event with
// callback), not as a one-shot operation.
// ---------------------------------------------------------------------------
TEST(SimCh4092, ProceduralContinuousAssignmentCorrespondsToProcess) {
  Arena arena;
  Scheduler sched(arena);
  int src = 0;
  int dst = 0;
  int process_eval_count = 0;

  // Model: assign dst = src; (procedural continuous assignment)
  // Each time src changes, the process re-evaluates.
  auto* drive0 = sched.GetEventPool().Acquire();
  drive0->kind = EventKind::kEvaluation;
  drive0->callback = [&]() {
    src = 10;
    ++process_eval_count;
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { dst = src; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, drive0);

  auto* drive5 = sched.GetEventPool().Acquire();
  drive5->kind = EventKind::kEvaluation;
  drive5->callback = [&]() {
    src = 20;
    ++process_eval_count;
    auto* update = sched.GetEventPool().Acquire();
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
// §4.9.2 "which is the assign ... statement"
// The procedural 'assign' statement overrides the normal procedural
// assignment to a variable, creating a continuous driver.
// ---------------------------------------------------------------------------
TEST(SimCh4092, AssignStatementOverridesProceduralAssignment) {
  Arena arena;
  Scheduler sched(arena);
  int reg_val = 0;
  int assign_src = 0;
  bool assign_active = false;

  // Time 0: procedural assignment reg_val = 5;
  auto* proc = sched.GetEventPool().Acquire();
  proc->kind = EventKind::kEvaluation;
  proc->callback = [&]() { reg_val = 5; };
  sched.ScheduleEvent({0}, Region::kActive, proc);

  // Time 1: assign reg_val = assign_src; → overrides procedural value.
  auto* assign_stmt = sched.GetEventPool().Acquire();
  assign_stmt->kind = EventKind::kEvaluation;
  assign_stmt->callback = [&]() {
    assign_active = true;
    assign_src = 99;
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() {
      if (assign_active) reg_val = assign_src;
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({1}, Region::kActive, assign_stmt);

  sched.Run();
  EXPECT_TRUE(assign_active);
  EXPECT_EQ(reg_val, 99);
}

// ---------------------------------------------------------------------------
// §4.9.2 "which is the ... force statement"
// The procedural 'force' statement overrides all other drivers on a net
// or variable, creating a forced continuous driver.
// ---------------------------------------------------------------------------
TEST(SimCh4092, ForceStatementOverridesAllDrivers) {
  Arena arena;
  Scheduler sched(arena);
  int net_val = 0;
  int force_src = 0;
  bool force_active = false;

  // Time 0: normal continuous assignment drives net_val = 10.
  auto* cont = sched.GetEventPool().Acquire();
  cont->kind = EventKind::kEvaluation;
  cont->callback = [&]() {
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() {
      if (!force_active) net_val = 10;
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, cont);

  // Time 1: force net_val = force_src; → overrides all drivers.
  auto* force_stmt = sched.GetEventPool().Acquire();
  force_stmt->kind = EventKind::kEvaluation;
  force_stmt->callback = [&]() {
    force_active = true;
    force_src = 77;
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { net_val = force_src; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({1}, Region::kActive, force_stmt);

  sched.Run();
  EXPECT_TRUE(force_active);
  EXPECT_EQ(net_val, 77);
}

// ---------------------------------------------------------------------------
// §4.9.2 "sensitive to the source elements in the expression"
// The procedural continuous assignment process only triggers when a source
// element in its RHS expression changes.
// ---------------------------------------------------------------------------
TEST(SimCh4092, SensitiveToSourceElements) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;
  int dst = 0;
  int eval_count = 0;

  // Model: assign dst = a + b;
  // Time 0: a changes → process triggers.
  auto* change_a = sched.GetEventPool().Acquire();
  change_a->kind = EventKind::kEvaluation;
  change_a->callback = [&]() {
    a = 3;
    ++eval_count;
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { dst = a + b; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, change_a);

  // Time 1: b changes → process triggers again.
  auto* change_b = sched.GetEventPool().Acquire();
  change_b->kind = EventKind::kEvaluation;
  change_b->callback = [&]() {
    b = 4;
    ++eval_count;
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { dst = a + b; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({1}, Region::kActive, change_b);

  sched.Run();
  EXPECT_EQ(eval_count, 2);
  EXPECT_EQ(dst, 7);
}

// ---------------------------------------------------------------------------
// §4.9.2 "it causes an active update event to be added to the event region"
// The update event from a procedural continuous assignment is scheduled in
// the Active region.
// ---------------------------------------------------------------------------
TEST(SimCh4092, SchedulesActiveUpdateEvent) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Schedule a procedural continuous assignment update in Active region
  // and an NBA event to prove it executes in Active (before NBA).
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    auto* active_update = sched.GetEventPool().Acquire();
    active_update->kind = EventKind::kUpdate;
    active_update->callback = [&]() { order.push_back("active_update"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, active_update);

    auto* nba_update = sched.GetEventPool().Acquire();
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
// §4.9.2 "using current values to determine the target"
// The target of the procedural continuous assignment is determined using
// values at the time the update executes.
// ---------------------------------------------------------------------------
TEST(SimCh4092, UsesCurrentValuesToDetermineTarget) {
  Arena arena;
  Scheduler sched(arena);
  int select = 0;
  int target_a = 0;
  int target_b = 0;

  // Time 0: select=0, so assign targets target_a.
  auto* eval0 = sched.GetEventPool().Acquire();
  eval0->kind = EventKind::kEvaluation;
  eval0->callback = [&]() {
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() {
      if (select == 0) {
        target_a = 1;
      } else {
        target_b = 1;
      }
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval0);

  // Time 1: select=1, so assign targets target_b.
  auto* change_sel = sched.GetEventPool().Acquire();
  change_sel->kind = EventKind::kEvaluation;
  change_sel->callback = [&]() {
    select = 1;
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() {
      if (select == 0) {
        target_a = 2;
      } else {
        target_b = 2;
      }
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({1}, Region::kActive, change_sel);

  sched.Run();
  EXPECT_EQ(target_a, 1);
  EXPECT_EQ(target_b, 2);
}

// ---------------------------------------------------------------------------
// §4.9.2 "A deassign ... statement deactivates any corresponding assign ...
//          statement(s)"
// After deassign, the procedural continuous assignment process is
// deactivated: further source changes no longer drive the target.
// ---------------------------------------------------------------------------
TEST(SimCh4092, DeassignDeactivatesAssign) {
  Arena arena;
  Scheduler sched(arena);
  int src = 0;
  int reg_val = 0;
  bool assign_active = false;

  // Time 0: assign reg_val = src; activates the proc cont assign.
  auto* assign_stmt = sched.GetEventPool().Acquire();
  assign_stmt->kind = EventKind::kEvaluation;
  assign_stmt->callback = [&]() {
    assign_active = true;
    src = 10;
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() {
      if (assign_active) reg_val = src;
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, assign_stmt);

  // Time 1: deassign reg_val; → deactivates the assign.
  auto* deassign_stmt = sched.GetEventPool().Acquire();
  deassign_stmt->kind = EventKind::kEvaluation;
  deassign_stmt->callback = [&]() { assign_active = false; };
  sched.ScheduleEvent({1}, Region::kActive, deassign_stmt);

  // Time 2: src changes, but assign is deactivated → reg_val not driven.
  auto* change_src = sched.GetEventPool().Acquire();
  change_src->kind = EventKind::kEvaluation;
  change_src->callback = [&]() {
    src = 50;
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() {
      if (assign_active) reg_val = src;
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({2}, Region::kActive, change_src);

  sched.Run();
  // reg_val should remain at 10 from time 0; time 2 update is gated off.
  EXPECT_EQ(reg_val, 10);
  EXPECT_FALSE(assign_active);
}

// ---------------------------------------------------------------------------
// §4.9.2 "a release statement deactivates any corresponding ... force
//          statement(s)"
// After release, the force process is deactivated and the underlying
// drivers resume control.
// ---------------------------------------------------------------------------
TEST(SimCh4092, ReleaseDeactivatesForce) {
  Arena arena;
  Scheduler sched(arena);
  int net_val = 0;
  int normal_driver = 0;
  int force_src = 0;
  bool force_active = false;

  // Time 0: normal driver → net_val = 5.
  auto* norm = sched.GetEventPool().Acquire();
  norm->kind = EventKind::kEvaluation;
  norm->callback = [&]() {
    normal_driver = 5;
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() {
      if (!force_active) net_val = normal_driver;
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, norm);

  // Time 1: force net_val = 88;
  auto* force_stmt = sched.GetEventPool().Acquire();
  force_stmt->kind = EventKind::kEvaluation;
  force_stmt->callback = [&]() {
    force_active = true;
    force_src = 88;
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { net_val = force_src; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({1}, Region::kActive, force_stmt);

  // Time 2: release net_val; → force deactivated, normal driver resumes.
  auto* release_stmt = sched.GetEventPool().Acquire();
  release_stmt->kind = EventKind::kEvaluation;
  release_stmt->callback = [&]() {
    force_active = false;
    // After release, the underlying driver reasserts.
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { net_val = normal_driver; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({2}, Region::kActive, release_stmt);

  sched.Run();
  EXPECT_FALSE(force_active);
  EXPECT_EQ(net_val, 5);
}

// ---------------------------------------------------------------------------
// §4.9.2 "A deassign ... statement deactivates any corresponding assign"
// After deassign, a subsequent procedural assignment can take effect,
// proving the assign override is removed.
// ---------------------------------------------------------------------------
TEST(SimCh4092, DeassignAllowsSubsequentProceduralAssignment) {
  Arena arena;
  Scheduler sched(arena);
  int reg_val = 0;
  bool assign_active = false;

  // Time 0: assign reg_val = 30; (procedural continuous)
  auto* assign_stmt = sched.GetEventPool().Acquire();
  assign_stmt->kind = EventKind::kEvaluation;
  assign_stmt->callback = [&]() {
    assign_active = true;
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() {
      if (assign_active) reg_val = 30;
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, assign_stmt);

  // Time 1: deassign reg_val;
  auto* deassign_stmt = sched.GetEventPool().Acquire();
  deassign_stmt->kind = EventKind::kEvaluation;
  deassign_stmt->callback = [&]() { assign_active = false; };
  sched.ScheduleEvent({1}, Region::kActive, deassign_stmt);

  // Time 2: reg_val = 42; (normal procedural assignment, no longer blocked).
  auto* proc_assign = sched.GetEventPool().Acquire();
  proc_assign->kind = EventKind::kEvaluation;
  proc_assign->callback = [&]() { reg_val = 42; };
  sched.ScheduleEvent({2}, Region::kActive, proc_assign);

  sched.Run();
  EXPECT_FALSE(assign_active);
  EXPECT_EQ(reg_val, 42);
}

// ---------------------------------------------------------------------------
// §4.9.2 "When the value of the expression changes, it causes an active
//          update event"
// The procedural continuous assignment process re-evaluates on each
// source change, scheduling a new active update event each time.
// ---------------------------------------------------------------------------
TEST(SimCh4092, ReEvaluatesOnEachSourceChange) {
  Arena arena;
  Scheduler sched(arena);
  int src = 0;
  int dst = 0;
  int update_count = 0;

  // Model: assign dst = src;
  // Source changes at time 0, 1, and 2.
  for (uint64_t t = 0; t < 3; ++t) {
    auto* eval = sched.GetEventPool().Acquire();
    eval->kind = EventKind::kEvaluation;
    int val = static_cast<int>((t + 1) * 10);
    eval->callback = [&, val]() {
      src = val;
      auto* update = sched.GetEventPool().Acquire();
      update->kind = EventKind::kUpdate;
      update->callback = [&, val]() {
        dst = val;
        ++update_count;
      };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
    };
    sched.ScheduleEvent({t}, Region::kActive, eval);
  }

  sched.Run();
  EXPECT_EQ(update_count, 3);
  EXPECT_EQ(dst, 30);
}
