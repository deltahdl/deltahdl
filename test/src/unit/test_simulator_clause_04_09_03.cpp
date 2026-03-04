#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(SimCh4093, ComputesRhsUsingCurrentValues) {
  Arena arena;
  Scheduler sched(arena);
  int src = 10;
  int captured_rhs = 0;
  int dst = 0;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {

    captured_rhs = src;

    auto* future = sched.GetEventPool().Acquire();
    future->kind = EventKind::kUpdate;
    future->callback = [&, captured_rhs]() { dst = captured_rhs; };
    sched.ScheduleEvent({5}, Region::kActive, future);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  auto* change_src = sched.GetEventPool().Acquire();
  change_src->kind = EventKind::kEvaluation;
  change_src->callback = [&]() { src = 99; };
  sched.ScheduleEvent({2}, Region::kActive, change_src);

  sched.Run();

  EXPECT_EQ(dst, 10);
  EXPECT_EQ(captured_rhs, 10);
}

TEST(SimCh4093, SuspendsProcessAndSchedulesFutureEvent) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    order.push_back("rhs_computed_t0");

    auto* resume = sched.GetEventPool().Acquire();
    resume->kind = EventKind::kUpdate;
    resume->callback = [&]() { order.push_back("assign_complete_t10"); };
    sched.ScheduleEvent({10}, Region::kActive, resume);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

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

TEST(SimCh4093, ZeroDelaySchedulesInactiveEvent) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    order.push_back("active_eval");

    auto* inactive_assign = sched.GetEventPool().Acquire();
    inactive_assign->kind = EventKind::kUpdate;
    inactive_assign->callback = [&]() { order.push_back("inactive_assign"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kInactive,
                        inactive_assign);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  auto* active2 = sched.GetEventPool().Acquire();
  active2->kind = EventKind::kEvaluation;
  active2->callback = [&]() { order.push_back("active_other"); };
  sched.ScheduleEvent({0}, Region::kActive, active2);

  sched.Run();

  ASSERT_GE(order.size(), 3u);
  EXPECT_EQ(order.back(), "inactive_assign");
}

TEST(SimCh4093, ZeroDelayFromReactiveSchedulesReInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* reactive_proc = sched.GetEventPool().Acquire();
  reactive_proc->kind = EventKind::kEvaluation;
  reactive_proc->callback = [&]() {
    order.push_back("reactive_eval");

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

TEST(SimCh4093, NoDelayAssignsImmediately) {
  Arena arena;
  Scheduler sched(arena);
  int dst = 0;
  bool next_stmt_executed = false;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {

    dst = 42;

    next_stmt_executed = true;
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(dst, 42);
  EXPECT_TRUE(next_stmt_executed);
}

TEST(SimCh4093, PerformsAssignmentToLhs) {
  Arena arena;
  Scheduler sched(arena);
  int dst = -1;

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

TEST(SimCh4093, EnablesEventsOnLhsUpdate) {
  Arena arena;
  Scheduler sched(arena);
  int sig = 0;
  bool sensitive_triggered = false;

  auto* blocking = sched.GetEventPool().Acquire();
  blocking->kind = EventKind::kEvaluation;
  blocking->callback = [&]() {
    int rhs_val = 5;
    auto* assign = sched.GetEventPool().Acquire();
    assign->kind = EventKind::kUpdate;
    assign->callback = [&, rhs_val]() {
      sig = rhs_val;

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

TEST(SimCh4093, TargetDeterminedAtResumeTime) {
  Arena arena;
  Scheduler sched(arena);
  int select = 0;
  int dst_a = 0;
  int dst_b = 0;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int rhs_val = 1;
    auto* assign = sched.GetEventPool().Acquire();
    assign->kind = EventKind::kUpdate;
    assign->callback = [&, rhs_val]() {

      if (select == 0) {
        dst_a = rhs_val;
      } else {
        dst_b = rhs_val;
      }
    };
    sched.ScheduleEvent({5}, Region::kActive, assign);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  auto* change_sel = sched.GetEventPool().Acquire();
  change_sel->kind = EventKind::kEvaluation;
  change_sel->callback = [&]() { select = 1; };
  sched.ScheduleEvent({3}, Region::kActive, change_sel);

  sched.Run();
  EXPECT_EQ(dst_a, 0);
  EXPECT_EQ(dst_b, 1);
}

TEST(SimCh4093, ContinuesWithNextSequentialStatement) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    order.push_back("before_assign");
    auto* resume = sched.GetEventPool().Acquire();
    resume->kind = EventKind::kUpdate;
    resume->callback = [&]() {
      order.push_back("assign_complete");

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

TEST(SimCh4093, ContinuesWithOtherActiveEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

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

  bool has_blocking = false;
  bool has_other = false;
  for (const auto& s : order) {
    if (s == "blocking_resume") has_blocking = true;
    if (s == "other_active") has_other = true;
  }
  EXPECT_TRUE(has_blocking);
  EXPECT_TRUE(has_other);
}
