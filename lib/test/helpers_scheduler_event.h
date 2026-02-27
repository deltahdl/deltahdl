#pragma once

#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "simulation/scheduler.h"

using namespace delta;

// Schedule a labeled event at time 0.
inline void ScheduleLabeled(Scheduler& sched, Region region,
                            const std::string& label,
                            std::vector<std::string>& order) {
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&order, label]() { order.push_back(label); };
  sched.ScheduleEvent({0}, region, ev);
}

// Schedule a labeled event at an explicit time.
inline void ScheduleLabeled(Scheduler& sched, uint64_t time, Region region,
                            const std::string& label,
                            std::vector<std::string>& order) {
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&order, label]() { order.push_back(label); };
  sched.ScheduleEvent({time}, region, ev);
}

// Verify that two regions execute in the given order.
inline void VerifyTwoRegionOrder(Region first, const std::string& first_label,
                                 Region second,
                                 const std::string& second_label) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;
  ScheduleLabeled(sched, second, second_label, order);
  ScheduleLabeled(sched, first, first_label, order);
  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], first_label);
  EXPECT_EQ(order[1], second_label);
}

// Verify that three regions execute in the given order.
inline void VerifyThreeRegionOrder(Region r1, const std::string& l1,
                                   Region r2, const std::string& l2,
                                   Region r3, const std::string& l3) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;
  ScheduleLabeled(sched, r3, l3, order);
  ScheduleLabeled(sched, r2, l2, order);
  ScheduleLabeled(sched, r1, l1, order);
  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], l1);
  EXPECT_EQ(order[1], l2);
  EXPECT_EQ(order[2], l3);
}
