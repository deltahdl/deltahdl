#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

static void ScheduleNbaAssign(Scheduler& sched, const int& src, int& dst) {
  int rhs_val = src;
  auto* nba = sched.GetEventPool().Acquire();
  nba->kind = EventKind::kUpdate;
  nba->callback = [&, rhs_val]() { dst = rhs_val; };
  sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
}

TEST(NonblockingAssignSchedulingSim, AlwaysComputesUpdatedValue) {
  Arena arena;
  Scheduler sched(arena);
  int src = 42;
  int dst = 0;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() { ScheduleNbaAssign(sched, src, dst); };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(dst, 42);
}

TEST(NonblockingAssignSchedulingSim, SchedulesUpdateAsNbaEvent) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&]() { order.push_back("nba_update"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);

    auto* active = sched.GetEventPool().Acquire();
    active->kind = EventKind::kUpdate;
    active->callback = [&]() { order.push_back("active_update"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, active);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "active_update");
  EXPECT_EQ(order[1], "nba_update");
}

TEST(NonblockingAssignSchedulingSim, ZeroDelaySchedulesNbaInCurrentTimestep) {
  Arena arena;
  Scheduler sched(arena);
  int dst = 0;
  bool nba_executed_at_time_zero = false;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int rhs_val = 5;
    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&, rhs_val]() {
      dst = rhs_val;
      nba_executed_at_time_zero = (sched.CurrentTime().ticks == 0);
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(dst, 5);
  EXPECT_TRUE(nba_executed_at_time_zero);
}

TEST(NonblockingAssignSchedulingSim, NonzeroDelaySchedulesNbaAsFutureEvent) {
  Arena arena;
  Scheduler sched(arena);
  int dst = 0;
  uint64_t nba_time = 0;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int rhs_val = 99;
    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&, rhs_val]() {
      dst = rhs_val;
      nba_time = sched.CurrentTime().ticks;
    };
    sched.ScheduleEvent({10}, Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(dst, 99);
  EXPECT_EQ(nba_time, 10u);
}

TEST(NonblockingAssignSchedulingSim, RhsComputedAtScheduleTime) {
  Arena arena;
  Scheduler sched(arena);
  int src = 10;
  int dst = 0;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    ScheduleNbaAssign(sched, src, dst);

    src = 99;
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();

  EXPECT_EQ(dst, 10);
}

TEST(NonblockingAssignSchedulingSim, LhsTargetDeterminedAtScheduleTime) {
  Arena arena;
  Scheduler sched(arena);
  int select = 0;
  int dst_a = 0;
  int dst_b = 0;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int target_select = select;
    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&, target_select]() {
      if (target_select == 0) {
        dst_a = 1;
      } else {
        dst_b = 1;
      }
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);

    select = 1;
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();

  EXPECT_EQ(dst_a, 1);
  EXPECT_EQ(dst_b, 0);
}

TEST(NonblockingAssignSchedulingSim, MultipleNbasAllScheduleInNbaRegion) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;
  int c = 0;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    auto* nba1 = sched.GetEventPool().Acquire();
    nba1->kind = EventKind::kUpdate;
    nba1->callback = [&]() { a = 1; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba1);

    auto* nba2 = sched.GetEventPool().Acquire();
    nba2->kind = EventKind::kUpdate;
    nba2->callback = [&]() { b = 2; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba2);

    auto* nba3 = sched.GetEventPool().Acquire();
    nba3->kind = EventKind::kUpdate;
    nba3->callback = [&]() { c = 3; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba3);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(a, 1);
  EXPECT_EQ(b, 2);
  EXPECT_EQ(c, 3);
}

TEST(NonblockingAssignSchedulingSim, NbaDoesNotBlockProcess) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    order.push_back("before_nba");

    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&]() { order.push_back("nba_update"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);

    order.push_back("after_nba_next_stmt");
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "before_nba");
  EXPECT_EQ(order[1], "after_nba_next_stmt");
  EXPECT_EQ(order[2], "nba_update");
}

TEST(NonblockingAssignSchedulingSim, NbaExecutesAfterActiveAndInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    auto* inactive = sched.GetEventPool().Acquire();
    inactive->kind = EventKind::kUpdate;
    inactive->callback = [&]() { order.push_back("inactive"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kInactive, inactive);

    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&]() { order.push_back("nba"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);

    order.push_back("active");
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "inactive");
  EXPECT_EQ(order[2], "nba");
}

TEST(NonblockingAssignSchedulingSim, SwapPatternBothRhsComputedBeforeUpdate) {
  Arena arena;
  Scheduler sched(arena);
  int x = 1;
  int y = 2;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int rhs_x = y;
    int rhs_y = x;

    auto* nba1 = sched.GetEventPool().Acquire();
    nba1->kind = EventKind::kUpdate;
    nba1->callback = [&, rhs_x]() { x = rhs_x; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba1);

    auto* nba2 = sched.GetEventPool().Acquire();
    nba2->kind = EventKind::kUpdate;
    nba2->callback = [&, rhs_y]() { y = rhs_y; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba2);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();

  EXPECT_EQ(x, 2);
  EXPECT_EQ(y, 1);
}
