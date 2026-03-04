#include <gtest/gtest.h>

#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(SimCh441, ActiveRegionSetMembership) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto schedule = [&](Region r, int id) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, id]() { order.push_back(id); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kActive, 1);
  schedule(Region::kInactive, 2);
  schedule(Region::kPreNBA, 3);
  schedule(Region::kNBA, 4);
  schedule(Region::kPostNBA, 5);

  sched.Run();
  ASSERT_EQ(order.size(), 5u);
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
  EXPECT_EQ(order[2], 3);
  EXPECT_EQ(order[3], 4);
  EXPECT_EQ(order[4], 5);
}

TEST(SimCh441, ReactiveRegionSetMembership) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto schedule = [&](Region r, int id) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, id]() { order.push_back(id); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kReactive, 1);
  schedule(Region::kReInactive, 2);
  schedule(Region::kPreReNBA, 3);
  schedule(Region::kReNBA, 4);
  schedule(Region::kPostReNBA, 5);

  sched.Run();
  ASSERT_EQ(order.size(), 5u);
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
  EXPECT_EQ(order[2], 3);
  EXPECT_EQ(order[3], 4);
  EXPECT_EQ(order[4], 5);
}

TEST(SimCh441, ActiveSetBeforeReactiveSet) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kReactive, "reactive", order);
  ScheduleLabeled(sched, Region::kActive, "active", order);
  ScheduleLabeled(sched, Region::kNBA, "nba", order);
  ScheduleLabeled(sched, Region::kReNBA, "renba", order);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "nba");
  EXPECT_EQ(order[2], "reactive");
  EXPECT_EQ(order[3], "renba");
}

TEST(SimCh441, IterativeRegionsAre14) {
  Arena arena;
  Scheduler sched(arena);

  const Region kIterative[] = {
      Region::kActive,     Region::kInactive,     Region::kPreNBA,
      Region::kNBA,        Region::kPostNBA,      Region::kPreObserved,
      Region::kObserved,   Region::kPostObserved, Region::kReactive,
      Region::kReInactive, Region::kPreReNBA,     Region::kReNBA,
      Region::kPostReNBA,  Region::kPrePostponed,
  };

  int count = 0;
  for (auto r : kIterative) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&count]() { count++; };
    sched.ScheduleEvent({0}, r, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 14);
}

TEST(SimCh441, NonIterativeRegionsAre3) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto schedule = [&](Region r, int id) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, id]() { order.push_back(id); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kPreponed, 1);
  schedule(Region::kPreActive, 2);
  schedule(Region::kPostponed, 3);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);

  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
  EXPECT_EQ(order[2], 3);
}

TEST(SimCh441, IterativePlusNonIterativeEquals17) {
  constexpr size_t kIterativeCount = 14;
  constexpr size_t kNonIterativeCount = 3;
  EXPECT_EQ(kIterativeCount + kNonIterativeCount, kRegionCount);
}

TEST(SimCh441, ActiveSetFeedbackReiterates) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() {
    order.push_back("active");

    auto* nba = sched.GetEventPool().Acquire();
    nba->callback = [&order]() { order.push_back("nba"); };
    sched.ScheduleEvent({0}, Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "nba");
}

TEST(SimCh441, ReactiveSetFeedbackReiterates) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() {
    order.push_back("reactive");
    auto* renba = sched.GetEventPool().Acquire();
    renba->callback = [&order]() { order.push_back("renba"); };
    sched.ScheduleEvent({0}, Region::kReNBA, renba);
  };
  sched.ScheduleEvent({0}, Region::kReactive, ev);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "reactive");
  EXPECT_EQ(order[1], "renba");
}

TEST(SimCh441, ReactiveRestartsActiveSetIteration) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* first = sched.GetEventPool().Acquire();
  first->callback = [&order]() { order.push_back("active1"); };
  sched.ScheduleEvent({0}, Region::kActive, first);

  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() {
    order.push_back("reactive");
    auto* active2 = sched.GetEventPool().Acquire();
    active2->callback = [&order]() { order.push_back("active2"); };
    sched.ScheduleEvent({0}, Region::kActive, active2);
  };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "active1");
  EXPECT_EQ(order[1], "reactive");
  EXPECT_EQ(order[2], "active2");
}

TEST(SimCh441, BothSetsInSameTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  int timestep_count = 0;

  sched.SetPostTimestepCallback([&]() { timestep_count++; });

  auto* active = sched.GetEventPool().Acquire();
  active->callback = []() {};
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = []() {};
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  sched.Run();
  EXPECT_EQ(timestep_count, 1);
}

TEST(SimCh441, ActiveSetCompletesBeforeObservedReactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kObserved, "observed", order);
  ScheduleLabeled(sched, Region::kActive, "active", order);
  ScheduleLabeled(sched, Region::kNBA, "nba", order);
  ScheduleLabeled(sched, Region::kInactive, "inactive", order);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "inactive");
  EXPECT_EQ(order[2], "nba");
  EXPECT_EQ(order[3], "observed");
}

TEST(SimCh441, ObservedRegionsBridgeActivAndReactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kActive, "active", order);
  ScheduleLabeled(sched, Region::kPreObserved, "pre_observed", order);
  ScheduleLabeled(sched, Region::kObserved, "observed", order);
  ScheduleLabeled(sched, Region::kPostObserved, "post_observed", order);
  ScheduleLabeled(sched, Region::kReactive, "reactive", order);

  sched.Run();
  ASSERT_EQ(order.size(), 5u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "pre_observed");
  EXPECT_EQ(order[2], "observed");
  EXPECT_EQ(order[3], "post_observed");
  EXPECT_EQ(order[4], "reactive");
}

TEST(SimCh441, PrePostponedIsLastIterativeRegion) {
  VerifyThreeRegionOrder({Region::kPostReNBA, "post_renba"},
                         {Region::kPrePostponed, "pre_postponed"},
                         {Region::kPostponed, "postponed"});
}

TEST(SimCh441, ProcessReactiveContextFlag) {
  Process proc;

  EXPECT_FALSE(proc.is_reactive);

  proc.is_reactive = true;
  EXPECT_TRUE(proc.is_reactive);
}

TEST(SimCh441, AllRegionsCategorizedAndProcessed) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int r = 0; r < static_cast<int>(Region::kCOUNT); ++r) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&count]() { count++; };
    sched.ScheduleEvent({0}, static_cast<Region>(r), ev);
  }

  sched.Run();
  EXPECT_EQ(count, static_cast<int>(kRegionCount));
}
