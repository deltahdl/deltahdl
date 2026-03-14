#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(SubroutineArgSchedulingSim, ArgumentPassedByValue) {
  Arena arena;
  Scheduler sched(arena);
  int caller_var = 10;
  int subroutine_local = 0;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    subroutine_local = caller_var;

    subroutine_local = 99;
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(caller_var, 10);
  EXPECT_EQ(subroutine_local, 99);
}

TEST(SubroutineArgSchedulingSim, CopyInOnInvocation) {
  Arena arena;
  Scheduler sched(arena);
  int src = 42;
  int copied_in = 0;

  auto* invoke = sched.GetEventPool().Acquire();
  invoke->kind = EventKind::kEvaluation;
  invoke->callback = [&]() { copied_in = src; };
  sched.ScheduleEvent({0}, Region::kActive, invoke);

  auto* change_src = sched.GetEventPool().Acquire();
  change_src->kind = EventKind::kEvaluation;
  change_src->callback = [&]() { src = 999; };
  sched.ScheduleEvent({3}, Region::kActive, change_src);

  sched.Run();

  EXPECT_EQ(copied_in, 42);
  EXPECT_EQ(src, 999);
}

TEST(SubroutineArgSchedulingSim, CopyOutOnReturn) {
  Arena arena;
  Scheduler sched(arena);
  int caller_dst = 0;
  bool returned = false;

  auto* invoke = sched.GetEventPool().Acquire();
  invoke->kind = EventKind::kEvaluation;
  invoke->callback = [&]() {
    int output_arg = 77;

    caller_dst = output_arg;
    returned = true;
  };
  sched.ScheduleEvent({0}, Region::kActive, invoke);

  sched.Run();
  EXPECT_TRUE(returned);
  EXPECT_EQ(caller_dst, 77);
}

TEST(SubroutineArgSchedulingSim, InoutArgCopiedInAndOut) {
  Arena arena;
  Scheduler sched(arena);
  int caller_var = 5;

  auto* invoke = sched.GetEventPool().Acquire();
  invoke->kind = EventKind::kEvaluation;
  invoke->callback = [&]() {
    int arg = caller_var;

    arg = arg + 10;

    caller_var = arg;
  };
  sched.ScheduleEvent({0}, Region::kActive, invoke);

  sched.Run();
  EXPECT_EQ(caller_var, 15);
}

TEST(SubroutineArgSchedulingSim, MultipleCopyOutArgsOnReturn) {
  Arena arena;
  Scheduler sched(arena);
  int dst_a = 0;
  int dst_b = 0;
  int dst_c = 0;

  auto* invoke = sched.GetEventPool().Acquire();
  invoke->kind = EventKind::kEvaluation;
  invoke->callback = [&]() {
    int out_a = 1;
    int out_b = 2;
    int out_c = 3;

    dst_a = out_a;
    dst_b = out_b;
    dst_c = out_c;
  };
  sched.ScheduleEvent({0}, Region::kActive, invoke);

  sched.Run();
  EXPECT_EQ(dst_a, 1);
  EXPECT_EQ(dst_b, 2);
  EXPECT_EQ(dst_c, 3);
}

TEST(SubroutineArgSchedulingSim, CopyOutBehavesAsBlockingAssignment) {
  Arena arena;
  Scheduler sched(arena);
  int result = 0;
  int observed_after_call = -1;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int out_arg = 42;
    result = out_arg;

    observed_after_call = result;
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(result, 42);
  EXPECT_EQ(observed_after_call, 42);
}

TEST(SubroutineArgSchedulingSim, CopyOutEnablesEventsOnUpdate) {
  Arena arena;
  Scheduler sched(arena);
  int sig = 0;
  bool sensitive_triggered = false;

  auto* invoke = sched.GetEventPool().Acquire();
  invoke->kind = EventKind::kEvaluation;
  invoke->callback = [&]() {
    int out_arg = 5;

    sig = out_arg;

    auto* sensitive = sched.GetEventPool().Acquire();
    sensitive->kind = EventKind::kEvaluation;
    sensitive->callback = [&]() { sensitive_triggered = true; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, sensitive);
  };
  sched.ScheduleEvent({0}, Region::kActive, invoke);

  sched.Run();
  EXPECT_EQ(sig, 5);
  EXPECT_TRUE(sensitive_triggered);
}

TEST(SubroutineArgSchedulingSim, CopyOutDoesNotSuspendProcess) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    order.push_back("before_call");

    int dst = 0;
    dst = 1;
    order.push_back("after_call");
    (void)dst;
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "before_call");
  EXPECT_EQ(order[1], "after_call");
}

TEST(SubroutineArgSchedulingSim, CopyOutOccursInActiveRegion) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    order.push_back("copyout_active");

    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&]() { order.push_back("nba_event"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "copyout_active");
  EXPECT_EQ(order[1], "nba_event");
}

TEST(SubroutineArgSchedulingSim, CopyInAndCopyOutAreIndependent) {
  Arena arena;
  Scheduler sched(arena);
  int caller_x = 10;
  int caller_y = 0;

  auto* invoke = sched.GetEventPool().Acquire();
  invoke->kind = EventKind::kEvaluation;
  invoke->callback = [&]() {
    int x_local = caller_x;

    int y_local = x_local * 2;

    caller_x = 999;

    caller_y = y_local;
  };
  sched.ScheduleEvent({0}, Region::kActive, invoke);

  sched.Run();

  EXPECT_EQ(caller_y, 20);

  EXPECT_EQ(caller_x, 999);
}
