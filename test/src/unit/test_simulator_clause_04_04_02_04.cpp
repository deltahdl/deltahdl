#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(NbaRegionSim, NBARegionExecutesEvents) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kNBA, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

TEST(NbaRegionSim, NBAExecutesAfterInactive) {
  VerifyTwoRegionOrder({Region::kInactive, "inactive"}, {Region::kNBA, "nba"});
}

TEST(NbaRegionSim, AllInactiveEventsCompleteBeforeNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  for (int i = 0; i < 3; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() {
      order.push_back("inactive" + std::to_string(i));
    };
    sched.ScheduleEvent({0}, Region::kInactive, ev);
  }

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { order.push_back("nba"); };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);

  EXPECT_EQ(order[3], "nba");
}

TEST(NbaRegionSim, NonblockingAssignmentSchedulesNBACurrentTime) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    order.push_back("active");

    auto* nba = sched.GetEventPool().Acquire();
    nba->callback = [&order]() { order.push_back("nba"); };
    sched.ScheduleEvent({0}, Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "nba");
}

TEST(NbaRegionSim, NonblockingAssignmentSchedulesNBALaterTime) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> nba_times;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    auto* nba = sched.GetEventPool().Acquire();
    nba->callback = [&nba_times, &sched]() {
      nba_times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({5}, Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  ASSERT_EQ(nba_times.size(), 1u);
  EXPECT_EQ(nba_times[0], 5u);
}

TEST(NbaRegionSim, NBAToActiveIteration) {
  VerifyIterationChain(Region::kActive, "active", Region::kNBA, "nba");
}

TEST(NbaRegionSim, NBAExecutesAfterActiveAndInactiveBeforeObserved) {
  VerifyFourRegionOrder({Region::kActive, "active"},
                        {Region::kInactive, "inactive"}, {Region::kNBA, "nba"},
                        {Region::kObserved, "observed"});
}

TEST(NbaRegionSim, NBAIsWithinActiveRegionSet) {
  auto nba_ord = static_cast<int>(Region::kNBA);
  auto inactive_ord = static_cast<int>(Region::kInactive);
  auto post_nba_ord = static_cast<int>(Region::kPostNBA);
  EXPECT_GT(nba_ord, inactive_ord);
  EXPECT_LT(nba_ord, post_nba_ord);
}

TEST(NbaRegionSim, NBAEventsAcrossMultipleTimeSlots) {
  VerifyEventsAcrossTimeSlots(Region::kNBA);
}

TEST(NbaRegionSim, NBAExecutesBeforeReNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto* ev_nba = sched.GetEventPool().Acquire();
  ev_nba->callback = [&order]() { order.push_back(1); };
  sched.ScheduleEvent({0}, Region::kNBA, ev_nba);

  auto* ev_renba = sched.GetEventPool().Acquire();
  ev_renba->callback = [&order]() { order.push_back(2); };
  sched.ScheduleEvent({0}, Region::kReNBA, ev_renba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
}

TEST(NbaRegionSim, NBARegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kNBA, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}
