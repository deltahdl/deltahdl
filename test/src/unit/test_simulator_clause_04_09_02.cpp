#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(SimCh4092, ProceduralContinuousAssignmentCorrespondsToProcess) {
  VerifyCACorrespondsToProcess();
}

TEST(SimCh4092, AssignStatementOverridesProceduralAssignment) {
  Arena arena;
  Scheduler sched(arena);
  int reg_val = 0;
  int assign_src = 0;
  bool assign_active = false;

  auto* proc = sched.GetEventPool().Acquire();
  proc->kind = EventKind::kEvaluation;
  proc->callback = [&]() { reg_val = 5; };
  sched.ScheduleEvent({0}, Region::kActive, proc);

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

TEST(SimCh4092, ForceStatementOverridesAllDrivers) {
  Arena arena;
  Scheduler sched(arena);
  int net_val = 0;
  int force_src = 0;
  bool force_active = false;

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

TEST(SimCh4092, SensitiveToSourceElements) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;
  int dst = 0;
  int eval_count = 0;

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

TEST(SimCh4092, SchedulesActiveUpdateEvent) {
  VerifyCASchedulesActiveUpdateEvent();
}

TEST(SimCh4092, UsesCurrentValuesToDetermineTarget) {
  Arena arena;
  Scheduler sched(arena);
  int select = 0;
  int target_a = 0;
  int target_b = 0;

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

TEST(SimCh4092, DeassignDeactivatesAssign) {
  Arena arena;
  Scheduler sched(arena);
  int src = 0;
  int reg_val = 0;
  bool assign_active = false;

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

  auto* deassign_stmt = sched.GetEventPool().Acquire();
  deassign_stmt->kind = EventKind::kEvaluation;
  deassign_stmt->callback = [&]() { assign_active = false; };
  sched.ScheduleEvent({1}, Region::kActive, deassign_stmt);

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

  EXPECT_EQ(reg_val, 10);
  EXPECT_FALSE(assign_active);
}

TEST(SimCh4092, ReleaseDeactivatesForce) {
  Arena arena;
  Scheduler sched(arena);
  int net_val = 0;
  int normal_driver = 0;
  int force_src = 0;
  bool force_active = false;

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

  auto* release_stmt = sched.GetEventPool().Acquire();
  release_stmt->kind = EventKind::kEvaluation;
  release_stmt->callback = [&]() {
    force_active = false;

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

TEST(SimCh4092, DeassignAllowsSubsequentProceduralAssignment) {
  Arena arena;
  Scheduler sched(arena);
  int reg_val = 0;
  bool assign_active = false;

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

  auto* deassign_stmt = sched.GetEventPool().Acquire();
  deassign_stmt->kind = EventKind::kEvaluation;
  deassign_stmt->callback = [&]() { assign_active = false; };
  sched.ScheduleEvent({1}, Region::kActive, deassign_stmt);

  auto* proc_assign = sched.GetEventPool().Acquire();
  proc_assign->kind = EventKind::kEvaluation;
  proc_assign->callback = [&]() { reg_val = 42; };
  sched.ScheduleEvent({2}, Region::kActive, proc_assign);

  sched.Run();
  EXPECT_FALSE(assign_active);
  EXPECT_EQ(reg_val, 42);
}

TEST(SimCh4092, ReEvaluatesOnEachSourceChange) {
  Arena arena;
  Scheduler sched(arena);
  int src = 0;
  int dst = 0;
  int update_count = 0;

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
