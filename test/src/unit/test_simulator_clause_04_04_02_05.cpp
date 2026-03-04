#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(SimCh4425, ObservedRegionExecutesEvents) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kObserved, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

TEST(SimCh4425, ObservedRegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kObserved, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(SimCh4425, ObservedSchedulesPassFailIntoReactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* obs = sched.GetEventPool().Acquire();
  obs->callback = [&]() {
    order.push_back("observed");

    auto* reactive = sched.GetEventPool().Acquire();
    reactive->callback = [&order]() { order.push_back("reactive"); };
    sched.ScheduleEvent({0}, Region::kReactive, reactive);
  };
  sched.ScheduleEvent({0}, Region::kObserved, obs);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "observed");
  EXPECT_EQ(order[1], "reactive");
}

TEST(SimCh4425, MultiplePassFailActionsScheduledInReactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* obs = sched.GetEventPool().Acquire();
  obs->callback = [&]() {
    order.push_back("observed");
    for (int i = 0; i < 3; ++i) {
      auto* r = sched.GetEventPool().Acquire();
      r->callback = [&order, i]() {
        order.push_back("reactive" + std::to_string(i));
      };
      sched.ScheduleEvent({0}, Region::kReactive, r);
    }
  };
  sched.ScheduleEvent({0}, Region::kObserved, obs);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "observed");

  EXPECT_EQ(order[1], "reactive0");
  EXPECT_EQ(order[2], "reactive1");
  EXPECT_EQ(order[3], "reactive2");
}

TEST(SimCh4425, ObservedExecutesAfterActiveRegionSet) {
  VerifyFourRegionOrder({Region::kActive, "active"},
                        {Region::kInactive, "inactive"}, {Region::kNBA, "nba"},
                        {Region::kObserved, "observed"});
}

TEST(SimCh4425, ObservedToActiveRestart) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* obs = sched.GetEventPool().Acquire();
  obs->callback = [&]() {
    order.push_back("observed");

    auto* act = sched.GetEventPool().Acquire();
    act->callback = [&order]() { order.push_back("active_restart"); };
    sched.ScheduleEvent({0}, Region::kActive, act);
  };
  sched.ScheduleEvent({0}, Region::kObserved, obs);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "observed");
  EXPECT_EQ(order[1], "active_restart");
}

TEST(SimCh4425, ObservedIsAfterPostNBABeforePostObserved) {
  auto observed_ord = static_cast<int>(Region::kObserved);
  auto post_nba_ord = static_cast<int>(Region::kPostNBA);
  auto post_observed_ord = static_cast<int>(Region::kPostObserved);
  EXPECT_GT(observed_ord, post_nba_ord);
  EXPECT_LT(observed_ord, post_observed_ord);
}

TEST(SimCh4425, PreObservedExecutesBeforeObserved) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* obs = sched.GetEventPool().Acquire();
  obs->callback = [&]() { order.push_back("observed"); };
  sched.ScheduleEvent({0}, Region::kObserved, obs);

  auto* pre_obs = sched.GetEventPool().Acquire();
  pre_obs->callback = [&]() { order.push_back("pre_observed"); };
  sched.ScheduleEvent({0}, Region::kPreObserved, pre_obs);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_observed");
  EXPECT_EQ(order[1], "observed");
}

TEST(SimCh4425, ObservedExecutesBeforePostObserved) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* post_obs = sched.GetEventPool().Acquire();
  post_obs->callback = [&]() { order.push_back("post_observed"); };
  sched.ScheduleEvent({0}, Region::kPostObserved, post_obs);

  auto* obs = sched.GetEventPool().Acquire();
  obs->callback = [&]() { order.push_back("observed"); };
  sched.ScheduleEvent({0}, Region::kObserved, obs);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "observed");
  EXPECT_EQ(order[1], "post_observed");
}

TEST(SimCh4425, ObservedEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kObserved, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}
