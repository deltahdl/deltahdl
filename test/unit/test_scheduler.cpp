#include <gtest/gtest.h>

#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

TEST(Scheduler, InitialState) {
  Scheduler sched;
  EXPECT_FALSE(sched.has_events());
  EXPECT_EQ(sched.current_time().ticks, 0);
}

TEST(Scheduler, ScheduleAndRunSingleEvent) {
  Scheduler sched;
  bool executed = false;
  Event ev;
  ev.kind = EventKind::Evaluation;
  ev.callback = [&executed]() { executed = true; };
  sched.schedule_event({0}, Region::Active, &ev);
  EXPECT_TRUE(sched.has_events());
  sched.run();
  EXPECT_TRUE(executed);
}

TEST(Scheduler, TimeOrdering) {
  Scheduler sched;
  std::vector<int> order;

  Event ev1;
  ev1.kind = EventKind::Evaluation;
  ev1.callback = [&order]() { order.push_back(1); };

  Event ev2;
  ev2.kind = EventKind::Evaluation;
  ev2.callback = [&order]() { order.push_back(2); };

  sched.schedule_event({10}, Region::Active, &ev2);
  sched.schedule_event({5}, Region::Active, &ev1);

  sched.run();
  ASSERT_EQ(order.size(), 2);
  EXPECT_EQ(order[0], 1);  // time 5 first
  EXPECT_EQ(order[1], 2);  // time 10 second
}

TEST(Scheduler, RegionOrderingWithinTimeSlot) {
  Scheduler sched;
  std::vector<int> order;

  Event ev_active;
  ev_active.kind = EventKind::Evaluation;
  ev_active.callback = [&order]() { order.push_back(1); };

  Event ev_nba;
  ev_nba.kind = EventKind::Evaluation;
  ev_nba.callback = [&order]() { order.push_back(2); };

  // Schedule NBA before Active, but Active should execute first
  sched.schedule_event({0}, Region::NBA, &ev_nba);
  sched.schedule_event({0}, Region::Active, &ev_active);

  sched.run();
  ASSERT_EQ(order.size(), 2);
  EXPECT_EQ(order[0], 1);  // Active first
  EXPECT_EQ(order[1], 2);  // NBA second
}
