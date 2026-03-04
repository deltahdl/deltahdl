#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(SimCh4429, PostponedRegionExecutesEvents) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kPostponed, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

TEST(SimCh4429, PostponedRegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPostponed, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(SimCh4429, PostponedObservesFinalState) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { value = 10; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { value = 20; };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() { value = 30; };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  auto* renba = sched.GetEventPool().Acquire();
  renba->callback = [&]() { value = 40; };
  sched.ScheduleEvent({0}, Region::kReNBA, renba);

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  EXPECT_EQ(sampled, 40);
}

TEST(SimCh4429, PostponedExecutesAfterAllOtherSimulationRegions) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kPostponed, "postponed", order);
  ScheduleLabeled(sched, Region::kReNBA, "renba", order);
  ScheduleLabeled(sched, Region::kReInactive, "reinactive", order);
  ScheduleLabeled(sched, Region::kReactive, "reactive", order);
  ScheduleLabeled(sched, Region::kObserved, "observed", order);
  ScheduleLabeled(sched, Region::kNBA, "nba", order);
  ScheduleLabeled(sched, Region::kInactive, "inactive", order);
  ScheduleLabeled(sched, Region::kActive, "active", order);

  sched.Run();
  ASSERT_EQ(order.size(), 8u);
  EXPECT_EQ(order[7], "postponed");
}

TEST(SimCh4429, PostponedIsLastRegionOrdinal) {
  auto postponed_ord = static_cast<int>(Region::kPostponed);
  auto pre_postponed_ord = static_cast<int>(Region::kPrePostponed);
  auto count_ord = static_cast<int>(Region::kCOUNT);
  EXPECT_GT(postponed_ord, pre_postponed_ord);
  EXPECT_EQ(postponed_ord + 1, count_ord);
}

TEST(SimCh4429, PostponedDoesNotReExecuteDuringIteration) {
  Arena arena;
  Scheduler sched(arena);
  int postponed_count = 0;

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { postponed_count++; };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    auto* nba = sched.GetEventPool().Acquire();
    nba->callback = [&]() {

      auto* act2 = sched.GetEventPool().Acquire();
      act2->callback = []() {};
      sched.ScheduleEvent({0}, Region::kActive, act2);
    };
    sched.ScheduleEvent({0}, Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  EXPECT_EQ(postponed_count, 1);
}

TEST(SimCh4429, PostponedAdvancesToNextTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* postponed0 = sched.GetEventPool().Acquire();
  postponed0->callback = [&]() { order.push_back("postponed_t0"); };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed0);

  auto* preponed1 = sched.GetEventPool().Acquire();
  preponed1->callback = [&]() { order.push_back("preponed_t1"); };
  sched.ScheduleEvent({1}, Region::kPreponed, preponed1);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "postponed_t0");
  EXPECT_EQ(order[1], "preponed_t1");
}

TEST(SimCh4429, PostponedPLIEventsExecuteInRegion) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* pli_ev = sched.GetEventPool().Acquire();
  pli_ev->callback = [&order]() { order.push_back("pli"); };
  sched.ScheduleEvent({0}, Region::kPostponed, pli_ev);

  auto* sim_ev = sched.GetEventPool().Acquire();
  sim_ev->callback = [&order]() { order.push_back("sim"); };
  sched.ScheduleEvent({0}, Region::kPostponed, sim_ev);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pli");
  EXPECT_EQ(order[1], "sim");
}

TEST(SimCh4429, PostponedEventsAcrossMultipleTimeSlots) {
  VerifyEventsAcrossTimeSlots(Region::kPostponed);
}

TEST(SimCh4429, PostponedStatePersistsToNextPreponed) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled_postponed = -1;
  int sampled_preponed = -1;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { value = 100; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { sampled_postponed = value; };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { sampled_preponed = value; };
  sched.ScheduleEvent({1}, Region::kPreponed, preponed);

  auto* active1 = sched.GetEventPool().Acquire();
  active1->callback = [&]() { value = 999; };
  sched.ScheduleEvent({1}, Region::kActive, active1);

  sched.Run();
  EXPECT_EQ(sampled_postponed, 100);
  EXPECT_EQ(sampled_preponed, 100);
}
