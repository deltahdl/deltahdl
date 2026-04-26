#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(ActiveRegionSim, ActiveRegionExecutesEvents) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

TEST(ActiveRegionSim, ActiveRegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(ActiveRegionSim, ActiveSelfLoopSchedulesMoreActiveEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() {
    order.push_back(1);
    auto* next = sched.GetEventPool().Acquire();
    next->callback = [&order]() { order.push_back(2); };
    sched.ScheduleEvent({0}, Region::kActive, next);
  };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
}

TEST(ActiveRegionSim, ActiveExecutesBeforeInactive) {
  VerifyTwoRegionOrder({Region::kActive, "active"},
                       {Region::kInactive, "inactive"});
}

TEST(ActiveRegionSim, ActiveIsWithinActiveRegionSet) {
  auto active_ord = static_cast<int>(Region::kActive);
  auto pre_active_ord = static_cast<int>(Region::kPreActive);
  auto post_nba_ord = static_cast<int>(Region::kPostNBA);
  EXPECT_GT(active_ord, pre_active_ord);
  EXPECT_LT(active_ord, post_nba_ord);
}

TEST(ActiveRegionSim, ActiveExecutesAfterPreponedAndPreActive) {
  VerifyThreeRegionOrder({Region::kPreponed, "preponed"},
                         {Region::kPreActive, "preactive"},
                         {Region::kActive, "active"});
}

TEST(ActiveRegionSim, ActiveEventsAcrossMultipleTimeSlots) {
  VerifyEventsAcrossTimeSlots(Region::kActive);
}

TEST(ActiveRegionSim, ActiveParticipatesInNBAIteration) {
  VerifyIterationChain(Region::kActive, "active", Region::kNBA, "nba");
}

TEST(ActiveRegionSim, ActiveRestartsFromReactiveRegion) {
  VerifyRegionRestart({Region::kActive, "active1"},
                      {Region::kReactive, "reactive"},
                      {Region::kActive, "active2"});
}

TEST(Scheduler, ScheduleAndRunSingleEvent) {
  Arena arena;
  Scheduler sched(arena);
  bool executed = false;
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&executed]() { executed = true; };
  sched.ScheduleEvent({0}, Region::kActive, ev);
  EXPECT_TRUE(sched.HasEvents());
  sched.Run();
  EXPECT_TRUE(executed);
}
