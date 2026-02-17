#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.9.3 Blocking assignment
//
// LRM §4.9.3:
//   "A blocking assignment statement (see 10.4.1) with an intra-assignment
//    delay computes the right-hand side value using the current values, then
//    causes the executing process to be suspended and scheduled as a future
//    event. If the delay is 0, the process is scheduled as an Inactive event
//    for the current time. If a blocking assignment with zero delay is
//    executed from a Reactive region, the process is scheduled as a
//    Re-Inactive event.
//
//    When the process is returned (or if it returns immediately if no delay
//    is specified), the process performs the assignment to the left-hand side
//    and enables any events based upon the update of the left-hand side. The
//    values at the time the process resumes are used to determine the
//    target(s). Execution may then continue with the next sequential
//    statement or with other Active or Reactive events."
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.9.3 "computes the right-hand side value using the current values"
// The RHS of a blocking assignment is evaluated using the values at the time
// the statement executes, not at the time the assignment completes.
// ---------------------------------------------------------------------------
TEST(SimCh4093, ComputesRhsUsingCurrentValues) {
  Arena arena;
  Scheduler sched(arena);
  int src = 10;
  int captured_rhs = 0;
  int dst = 0;

  // Model: dst = #5 src;
  // At time 0, src=10 → capture RHS=10. At time 5, assign dst=10 even if
  // src has changed by then.
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    // Compute RHS using current values.
    captured_rhs = src;
    // Schedule future assignment at time 5.
    auto* future = sched.GetEventPool().Acquire();
    future->kind = EventKind::kUpdate;
    future->callback = [&, captured_rhs]() { dst = captured_rhs; };
    sched.ScheduleEvent({5}, Region::kActive, future);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  // Change src at time 2, before the delayed assignment completes.
  auto* change_src = sched.GetEventPool().Acquire();
  change_src->kind = EventKind::kEvaluation;
  change_src->callback = [&]() { src = 99; };
  sched.ScheduleEvent({2}, Region::kActive, change_src);

  sched.Run();
  // dst should be 10 (captured at time 0), not 99.
  EXPECT_EQ(dst, 10);
  EXPECT_EQ(captured_rhs, 10);
}

// ---------------------------------------------------------------------------
// §4.9.3 "causes the executing process to be suspended and scheduled as a
//          future event"
// An intra-assignment delay suspends the process until the specified future
// time, when the assignment completes.
// ---------------------------------------------------------------------------
TEST(SimCh4093, SuspendsProcessAndSchedulesFutureEvent) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Model: dst = #10 src; followed by next_statement;
  // The process suspends at the delay and resumes at time 10.
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    order.push_back("rhs_computed_t0");
    // Schedule the assignment completion at time 10.
    auto* resume = sched.GetEventPool().Acquire();
    resume->kind = EventKind::kUpdate;
    resume->callback = [&]() { order.push_back("assign_complete_t10"); };
    sched.ScheduleEvent({10}, Region::kActive, resume);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  // Another event at time 5 to show the process was suspended during it.
  auto* mid = sched.GetEventPool().Acquire();
  mid->kind = EventKind::kEvaluation;
  mid->callback = [&]() { order.push_back("other_event_t5"); };
  sched.ScheduleEvent({5}, Region::kActive, mid);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "rhs_computed_t0");
  EXPECT_EQ(order[1], "other_event_t5");
  EXPECT_EQ(order[2], "assign_complete_t10");
}

// ---------------------------------------------------------------------------
// §4.9.3 "If the delay is 0, the process is scheduled as an Inactive event
//          for the current time"
// A blocking assignment with #0 delay schedules the process in the Inactive
// region of the current time step, not the Active region.
// ---------------------------------------------------------------------------
TEST(SimCh4093, ZeroDelaySchedulesInactiveEvent) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Model: dst = #0 src;
  // The assignment is scheduled in the Inactive region of the current time.
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    order.push_back("active_eval");
    // #0 delay → schedule in Inactive region.
    auto* inactive_assign = sched.GetEventPool().Acquire();
    inactive_assign->kind = EventKind::kUpdate;
    inactive_assign->callback = [&]() { order.push_back("inactive_assign"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kInactive,
                        inactive_assign);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  // Another Active event at same time to show Inactive executes after Active.
  auto* active2 = sched.GetEventPool().Acquire();
  active2->kind = EventKind::kEvaluation;
  active2->callback = [&]() { order.push_back("active_other"); };
  sched.ScheduleEvent({0}, Region::kActive, active2);

  sched.Run();
  // Both Active events execute before the Inactive assignment.
  ASSERT_GE(order.size(), 3u);
  EXPECT_EQ(order.back(), "inactive_assign");
}

// ---------------------------------------------------------------------------
// §4.9.3 "If a blocking assignment with zero delay is executed from a
//          Reactive region, the process is scheduled as a Re-Inactive event"
// When the blocking assignment with #0 originates in the Reactive region,
// the process goes to Re-Inactive instead of Inactive.
// ---------------------------------------------------------------------------
TEST(SimCh4093, ZeroDelayFromReactiveSchedulesReInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // A Reactive-region process executing a #0 blocking assignment.
  auto* reactive_proc = sched.GetEventPool().Acquire();
  reactive_proc->kind = EventKind::kEvaluation;
  reactive_proc->callback = [&]() {
    order.push_back("reactive_eval");
    // #0 delay from Reactive → Re-Inactive.
    auto* reinactive = sched.GetEventPool().Acquire();
    reinactive->kind = EventKind::kUpdate;
    reinactive->callback = [&]() { order.push_back("reinactive_assign"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kReInactive, reinactive);
  };
  sched.ScheduleEvent({0}, Region::kReactive, reactive_proc);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "reactive_eval");
  EXPECT_EQ(order[1], "reinactive_assign");
}

// ---------------------------------------------------------------------------
// §4.9.3 "if it returns immediately if no delay is specified"
// A blocking assignment without an intra-assignment delay performs the
// assignment immediately — the process is not suspended.
// ---------------------------------------------------------------------------
TEST(SimCh4093, NoDelayAssignsImmediately) {
  Arena arena;
  Scheduler sched(arena);
  int dst = 0;
  bool next_stmt_executed = false;

  // Model: dst = 42; next_stmt;
  // No delay → assignment completes immediately, execution continues.
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    // Immediate blocking assignment.
    dst = 42;
    // Next sequential statement executes immediately after.
    next_stmt_executed = true;
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(dst, 42);
  EXPECT_TRUE(next_stmt_executed);
}

// ---------------------------------------------------------------------------
// §4.9.3 "the process performs the assignment to the left-hand side"
// After the delay, the captured RHS value is assigned to the LHS.
// ---------------------------------------------------------------------------
TEST(SimCh4093, PerformsAssignmentToLhs) {
  Arena arena;
  Scheduler sched(arena);
  int dst = -1;

  // Model: dst = #3 77;
  // RHS=77 captured, assigned to dst at time 3.
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int rhs_val = 77;
    auto* assign = sched.GetEventPool().Acquire();
    assign->kind = EventKind::kUpdate;
    assign->callback = [&, rhs_val]() { dst = rhs_val; };
    sched.ScheduleEvent({3}, Region::kActive, assign);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(dst, 77);
}

// ---------------------------------------------------------------------------
// §4.9.3 "enables any events based upon the update of the left-hand side"
// When the blocking assignment completes and updates the LHS, any processes
// sensitive to the LHS are triggered.
// ---------------------------------------------------------------------------
TEST(SimCh4093, EnablesEventsOnLhsUpdate) {
  Arena arena;
  Scheduler sched(arena);
  int sig = 0;
  bool sensitive_triggered = false;

  // Model: sig = #2 5; and a process sensitive to sig.
  auto* blocking = sched.GetEventPool().Acquire();
  blocking->kind = EventKind::kEvaluation;
  blocking->callback = [&]() {
    int rhs_val = 5;
    auto* assign = sched.GetEventPool().Acquire();
    assign->kind = EventKind::kUpdate;
    assign->callback = [&, rhs_val]() {
      sig = rhs_val;
      // The update triggers events sensitive to sig.
      auto* sensitive = sched.GetEventPool().Acquire();
      sensitive->kind = EventKind::kEvaluation;
      sensitive->callback = [&]() { sensitive_triggered = true; };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, sensitive);
    };
    sched.ScheduleEvent({2}, Region::kActive, assign);
  };
  sched.ScheduleEvent({0}, Region::kActive, blocking);

  sched.Run();
  EXPECT_EQ(sig, 5);
  EXPECT_TRUE(sensitive_triggered);
}

// ---------------------------------------------------------------------------
// §4.9.3 "The values at the time the process resumes are used to determine
//          the target(s)"
// For a blocking assignment with delay where the LHS target depends on
// some variable, the target is determined at resume time, not schedule time.
// ---------------------------------------------------------------------------
TEST(SimCh4093, TargetDeterminedAtResumeTime) {
  Arena arena;
  Scheduler sched(arena);
  int select = 0;
  int dst_a = 0;
  int dst_b = 0;

  // Model: (select ? dst_b : dst_a) = #5 1;
  // At time 0, select=0 → would target dst_a. But select changes at time 3.
  // At resume time 5, select=1 → targets dst_b instead.
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int rhs_val = 1;
    auto* assign = sched.GetEventPool().Acquire();
    assign->kind = EventKind::kUpdate;
    assign->callback = [&, rhs_val]() {
      // Target determined at resume time using current select value.
      if (select == 0) {
        dst_a = rhs_val;
      } else {
        dst_b = rhs_val;
      }
    };
    sched.ScheduleEvent({5}, Region::kActive, assign);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  // Change select at time 3.
  auto* change_sel = sched.GetEventPool().Acquire();
  change_sel->kind = EventKind::kEvaluation;
  change_sel->callback = [&]() { select = 1; };
  sched.ScheduleEvent({3}, Region::kActive, change_sel);

  sched.Run();
  EXPECT_EQ(dst_a, 0);
  EXPECT_EQ(dst_b, 1);
}

// ---------------------------------------------------------------------------
// §4.9.3 "Execution may then continue with the next sequential statement"
// After the blocking assignment completes (with or without delay), the next
// sequential statement in the process executes.
// ---------------------------------------------------------------------------
TEST(SimCh4093, ContinuesWithNextSequentialStatement) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Model: begin dst = #2 val; next_stmt; end
  // After the delayed assignment at time 2, the next statement runs.
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    order.push_back("before_assign");
    auto* resume = sched.GetEventPool().Acquire();
    resume->kind = EventKind::kUpdate;
    resume->callback = [&]() {
      order.push_back("assign_complete");
      // Next sequential statement after blocking assignment.
      order.push_back("next_statement");
    };
    sched.ScheduleEvent({2}, Region::kActive, resume);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "before_assign");
  EXPECT_EQ(order[1], "assign_complete");
  EXPECT_EQ(order[2], "next_statement");
}

// ---------------------------------------------------------------------------
// §4.9.3 "or with other Active or Reactive events"
// After a blocking assignment completes, other events in the same region
// may execute (the scheduler continues processing the region).
// ---------------------------------------------------------------------------
TEST(SimCh4093, ContinuesWithOtherActiveEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Two processes at time 2: the resumed blocking assignment and another
  // independent Active event. Both execute in the Active region.
  auto* blocking = sched.GetEventPool().Acquire();
  blocking->kind = EventKind::kEvaluation;
  blocking->callback = [&]() {
    auto* resume = sched.GetEventPool().Acquire();
    resume->kind = EventKind::kUpdate;
    resume->callback = [&]() { order.push_back("blocking_resume"); };
    sched.ScheduleEvent({2}, Region::kActive, resume);
  };
  sched.ScheduleEvent({0}, Region::kActive, blocking);

  auto* other = sched.GetEventPool().Acquire();
  other->kind = EventKind::kEvaluation;
  other->callback = [&]() { order.push_back("other_active"); };
  sched.ScheduleEvent({2}, Region::kActive, other);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  // Both events execute at time 2 in Active region (order is nondeterministic
  // per §4.7, but both must execute).
  bool has_blocking = false;
  bool has_other = false;
  for (const auto& s : order) {
    if (s == "blocking_resume") has_blocking = true;
    if (s == "other_active") has_other = true;
  }
  EXPECT_TRUE(has_blocking);
  EXPECT_TRUE(has_other);
}
