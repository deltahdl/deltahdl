#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(SimCh49, ContinuousAssignmentAsProcessAndEvent) {
  Arena arena;
  Scheduler sched(arena);
  int src = 0;
  int dst = 0;

  auto* process = sched.GetEventPool().Acquire();
  process->kind = EventKind::kEvaluation;
  process->callback = [&]() {
    src = 5;

    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { dst = src; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, process);

  sched.Run();
  EXPECT_EQ(dst, 5);
}

TEST(SimCh49, ProceduralContinuousAssignmentAsProcessAndEvent) {
  Arena arena;
  Scheduler sched(arena);
  int forced_val = 0;
  bool force_active = true;

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

  auto* release_proc = sched.GetEventPool().Acquire();
  release_proc->kind = EventKind::kEvaluation;
  release_proc->callback = [&]() { force_active = false; };
  sched.ScheduleEvent({1}, Region::kActive, release_proc);

  sched.Run();
  EXPECT_EQ(forced_val, 42);
  EXPECT_FALSE(force_active);
}

TEST(SimCh49, BlockingAssignmentAsProcessAndEvent) {
  Arena arena;
  Scheduler sched(arena);
  int result = 0;
  SimTime resume_time{0};

  auto* proc = sched.GetEventPool().Acquire();
  proc->kind = EventKind::kEvaluation;
  proc->callback = [&]() {
    int rhs = 99;

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

TEST(SimCh49, BlockingAssignmentZeroDelaySchedulesInactive) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  std::vector<std::string> order;

  auto* proc = sched.GetEventPool().Acquire();
  proc->kind = EventKind::kEvaluation;
  proc->callback = [&]() {
    order.push_back("active");
    int rhs = 10;

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

TEST(SimCh49, NonblockingAssignmentAsNBAEvent) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;

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

TEST(SimCh49, SwitchProcessingAsActiveEvents) {
  Arena arena;
  Scheduler sched(arena);
  int node_a = 0;
  int node_b = 0;

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

TEST(SimCh49, PortConnectionAsImplicitContinuousAssignment) {
  Arena arena;
  Scheduler sched(arena);
  int outside_sig = 0;
  int local_input = 0;

  auto* driver = sched.GetEventPool().Acquire();
  driver->kind = EventKind::kEvaluation;
  driver->callback = [&]() {
    outside_sig = 7;

    auto* port_update = sched.GetEventPool().Acquire();
    port_update->kind = EventKind::kUpdate;
    port_update->callback = [&]() { local_input = outside_sig; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, port_update);
  };
  sched.ScheduleEvent({0}, Region::kActive, driver);

  sched.Run();
  EXPECT_EQ(local_input, 7);
}

TEST(SimCh49, SubroutineArgumentPassingAsBlockingAssignment) {
  Arena arena;
  Scheduler sched(arena);
  int caller_arg = 10;
  int callee_local = 0;
  int caller_out = 0;

  auto* call = sched.GetEventPool().Acquire();
  call->kind = EventKind::kEvaluation;
  call->callback = [&]() {
    callee_local = caller_arg;

    callee_local += 5;

    caller_out = callee_local;
  };
  sched.ScheduleEvent({0}, Region::kActive, call);

  sched.Run();
  EXPECT_EQ(caller_out, 15);
}

TEST(SimCh49, AllAssignmentTypesUseSchedulerInfrastructure) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> executed;

  ScheduleLabeled(sched, Region::kActive, "continuous", executed);
  ScheduleLabeled(sched, Region::kActive, "proc_continuous", executed);
  ScheduleLabeled(sched, Region::kInactive, "blocking", executed);
  ScheduleLabeled(sched, Region::kNBA, "nonblocking", executed);
  ScheduleLabeled(sched, Region::kActive, "switch", executed);
  ScheduleLabeled(sched, Region::kActive, "port", executed);
  ScheduleLabeled(sched, Region::kActive, "subroutine", executed);

  sched.Run();
  EXPECT_EQ(executed.size(), 7u);
}

TEST(SimCh49, AssignmentOrderingFollowsRegionOrdering) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* cont = sched.GetEventPool().Acquire();
  cont->kind = EventKind::kUpdate;
  cont->callback = [&]() { order.push_back("continuous_active"); };
  sched.ScheduleEvent({0}, Region::kActive, cont);

  auto* blk = sched.GetEventPool().Acquire();
  blk->kind = EventKind::kEvaluation;
  blk->callback = [&]() { order.push_back("blocking_inactive"); };
  sched.ScheduleEvent({0}, Region::kInactive, blk);

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
