#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(SimCh4421, PreponedExecutesBeforeAllOtherRegions) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kPostponed, "postponed", order);
  ScheduleLabeled(sched, Region::kReactive, "reactive", order);
  ScheduleLabeled(sched, Region::kObserved, "observed", order);
  ScheduleLabeled(sched, Region::kNBA, "nba", order);
  ScheduleLabeled(sched, Region::kActive, "active", order);
  ScheduleLabeled(sched, Region::kPreponed, "preponed", order);

  sched.Run();
  ASSERT_GE(order.size(), 1u);
  EXPECT_EQ(order[0], "preponed");
}

TEST(SimCh4421, PreponedSamplesBeforeActiveModifications) {
  Arena arena;
  Scheduler sched(arena);
  int shared_value = 0;
  int sampled_in_preponed = -1;
  int sampled_in_active = -1;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    shared_value = 42;
    sampled_in_active = shared_value;
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { sampled_in_preponed = shared_value; };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_EQ(sampled_in_preponed, 0);
  EXPECT_EQ(sampled_in_active, 42);
}

TEST(SimCh4421, PreponedEquivalentToPreviousPostponed) {
  Arena arena;
  Scheduler sched(arena);
  int shared_value = 0;
  int sampled_in_postponed = -1;
  int sampled_in_preponed = -1;

  auto* active0 = sched.GetEventPool().Acquire();
  active0->callback = [&]() { shared_value = 100; };
  sched.ScheduleEvent({0}, Region::kActive, active0);

  auto* postponed0 = sched.GetEventPool().Acquire();
  postponed0->callback = [&]() { sampled_in_postponed = shared_value; };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed0);

  auto* preponed1 = sched.GetEventPool().Acquire();
  preponed1->callback = [&]() { sampled_in_preponed = shared_value; };
  sched.ScheduleEvent({1}, Region::kPreponed, preponed1);

  auto* active1 = sched.GetEventPool().Acquire();
  active1->callback = [&]() { shared_value = 999; };
  sched.ScheduleEvent({1}, Region::kActive, active1);

  sched.Run();
  EXPECT_EQ(sampled_in_postponed, 100);
  EXPECT_EQ(sampled_in_preponed, 100);
}

TEST(SimCh4421, PreponedDoesNotReExecuteDuringIteration) {
  Arena arena;
  Scheduler sched(arena);
  int preponed_count = 0;

  auto* prep = sched.GetEventPool().Acquire();
  prep->callback = [&]() { preponed_count++; };
  sched.ScheduleEvent({0}, Region::kPreponed, prep);

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    auto* nba = sched.GetEventPool().Acquire();
    nba->callback = []() {};
    sched.ScheduleEvent({0}, Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  EXPECT_EQ(preponed_count, 1);
}

TEST(SimCh4421, PreponedPLIEventsExecuteInRegion) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* pli_ev = sched.GetEventPool().Acquire();
  pli_ev->callback = [&order]() { order.push_back("pli"); };
  sched.ScheduleEvent({0}, Region::kPreponed, pli_ev);

  auto* sim_ev = sched.GetEventPool().Acquire();
  sim_ev->callback = [&order]() { order.push_back("sim"); };
  sched.ScheduleEvent({0}, Region::kPreponed, sim_ev);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pli");
  EXPECT_EQ(order[1], "sim");
}

TEST(SimCh4421, PreponedRunsOncePerTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  int preponed_count = 0;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { preponed_count++; };
    sched.ScheduleEvent({t}, Region::kPreponed, ev);
  }

  sched.Run();
  EXPECT_EQ(preponed_count, 3);
}

TEST(SimCh4421, OneStepDelayMechanismViaPreponedRegion) {
  Arena arena;
  Scheduler sched(arena);
  int value = 10;
  int one_step_sample = -1;

  auto* act0 = sched.GetEventPool().Acquire();
  act0->callback = [&]() { value = 20; };
  sched.ScheduleEvent({0}, Region::kActive, act0);

  auto* prep1 = sched.GetEventPool().Acquire();
  prep1->callback = [&]() { one_step_sample = value; };
  sched.ScheduleEvent({1}, Region::kPreponed, prep1);

  auto* act1 = sched.GetEventPool().Acquire();
  act1->callback = [&]() { value = 30; };
  sched.ScheduleEvent({1}, Region::kActive, act1);

  sched.Run();
  EXPECT_EQ(one_step_sample, 20);
  EXPECT_EQ(value, 30);
}

TEST(SimCh4421, PreponedNotReExecutedByReactiveToActiveRestart) {
  Arena arena;
  Scheduler sched(arena);
  int preponed_count = 0;

  auto* prep = sched.GetEventPool().Acquire();
  prep->callback = [&]() { preponed_count++; };
  sched.ScheduleEvent({0}, Region::kPreponed, prep);

  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() {
    auto* active2 = sched.GetEventPool().Acquire();
    active2->callback = []() {};
    sched.ScheduleEvent({0}, Region::kActive, active2);
  };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  sched.Run();
  EXPECT_EQ(preponed_count, 1);
}

TEST(SimCh4421, PreponedIsOrdinalZero) {
  EXPECT_EQ(static_cast<int>(Region::kPreponed), 0);
}

TEST(SimCh4421, PreponedSeesCorrectStateAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  std::vector<int> preponed_samples;

  auto* act0 = sched.GetEventPool().Acquire();
  act0->callback = [&]() { value = 10; };
  sched.ScheduleEvent({0}, Region::kActive, act0);

  auto* prep1 = sched.GetEventPool().Acquire();
  prep1->callback = [&]() { preponed_samples.push_back(value); };
  sched.ScheduleEvent({1}, Region::kPreponed, prep1);

  auto* act1 = sched.GetEventPool().Acquire();
  act1->callback = [&]() { value = 20; };
  sched.ScheduleEvent({1}, Region::kActive, act1);

  auto* prep2 = sched.GetEventPool().Acquire();
  prep2->callback = [&]() { preponed_samples.push_back(value); };
  sched.ScheduleEvent({2}, Region::kPreponed, prep2);

  sched.Run();
  ASSERT_EQ(preponed_samples.size(), 2u);
  EXPECT_EQ(preponed_samples[0], 10);
  EXPECT_EQ(preponed_samples[1], 20);
}
