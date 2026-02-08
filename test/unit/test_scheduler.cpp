#include <gtest/gtest.h>

#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

TEST(Scheduler, InitialState) {
  Scheduler sched;
  EXPECT_FALSE(sched.HasEvents());
  EXPECT_EQ(sched.CurrentTime().ticks, 0);
}

TEST(Scheduler, ScheduleAndRunSingleEvent) {
  Scheduler sched;
  bool executed = false;
  Event ev;
  ev.kind = EventKind::kEvaluation;
  ev.callback = [&executed]() { executed = true; };
  sched.ScheduleEvent({0}, Region::kActive, &ev);
  EXPECT_TRUE(sched.HasEvents());
  sched.Run();
  EXPECT_TRUE(executed);
}

TEST(Scheduler, TimeOrdering) {
  Scheduler sched;
  std::vector<int> order;

  Event ev1;
  ev1.kind = EventKind::kEvaluation;
  ev1.callback = [&order]() { order.push_back(1); };

  Event ev2;
  ev2.kind = EventKind::kEvaluation;
  ev2.callback = [&order]() { order.push_back(2); };

  sched.ScheduleEvent({10}, Region::kActive, &ev2);
  sched.ScheduleEvent({5}, Region::kActive, &ev1);

  sched.Run();
  ASSERT_EQ(order.size(), 2);
  EXPECT_EQ(order[0], 1);  // time 5 first
  EXPECT_EQ(order[1], 2);  // time 10 second
}

TEST(Scheduler, RegionOrderingWithinTimeSlot) {
  Scheduler sched;
  std::vector<int> order;

  Event ev_active;
  ev_active.kind = EventKind::kEvaluation;
  ev_active.callback = [&order]() { order.push_back(1); };

  Event ev_nba;
  ev_nba.kind = EventKind::kEvaluation;
  ev_nba.callback = [&order]() { order.push_back(2); };

  // Schedule NBA before Active, but Active should execute first
  sched.ScheduleEvent({0}, Region::kNBA, &ev_nba);
  sched.ScheduleEvent({0}, Region::kActive, &ev_active);

  sched.Run();
  ASSERT_EQ(order.size(), 2);
  EXPECT_EQ(order[0], 1);  // Active first
  EXPECT_EQ(order[1], 2);  // NBA second
}
