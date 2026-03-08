// Non-LRM tests

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_scheduler_event.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SimCh45, ExecuteSimulationStartsAtTimeZero) {
  Arena arena;
  Scheduler sched(arena);
  uint64_t observed_time = UINT64_MAX;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { observed_time = sched.CurrentTime().ticks; };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  EXPECT_EQ(observed_time, 0u);
}

TEST(SimCh45, ExecuteSimulationAdvancesThroughNonemptyTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t : {0, 5, 10}) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 5u);
  EXPECT_EQ(times[2], 10u);
}

TEST(SimCh45, ExecuteSimulationStopsWhenAllTimeSlotsEmpty) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { count++; };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  EXPECT_EQ(count, 1);

  EXPECT_FALSE(sched.HasEvents());
}

TEST(SimCh45, ExecuteTimeSlotFullRegionOrdering) { VerifyAllRegionOrder(); }

TEST(SimCh45, ActiveSetIterationReExecutesActiveAfterInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* inactive = sched.GetEventPool().Acquire();
  inactive->callback = [&]() {
    order.push_back("inactive");
    auto* new_active = sched.GetEventPool().Acquire();
    new_active->callback = [&]() { order.push_back("active_from_inactive"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, new_active);
  };
  sched.ScheduleEvent({0}, Region::kInactive, inactive);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "inactive");
  EXPECT_EQ(order[1], "active_from_inactive");
}

TEST(SimCh45, ActiveSetReIteratesWhenNBAGeneratesActiveEvent) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() {
    order.push_back("nba");
    auto* new_active = sched.GetEventPool().Acquire();
    new_active->callback = [&]() { order.push_back("active_from_nba"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, new_active);
  };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "nba");
  EXPECT_EQ(order[1], "active_from_nba");
}

TEST(SimCh45, ReactiveSetReIteratesWhenReInactiveGeneratesReactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* re_inactive = sched.GetEventPool().Acquire();
  re_inactive->callback = [&]() {
    order.push_back("re_inactive");
    auto* new_reactive = sched.GetEventPool().Acquire();
    new_reactive->callback = [&]() {
      order.push_back("reactive_from_re_inactive");
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kReactive, new_reactive);
  };
  sched.ScheduleEvent({0}, Region::kReInactive, re_inactive);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "re_inactive");
  EXPECT_EQ(order[1], "reactive_from_re_inactive");
}

TEST(SimCh45, PrePostponedOnlyAfterActiveAndReactiveSetsEmpty) {
  VerifyThreeRegionOrder({Region::kActive, "active"},
                         {Region::kReactive, "reactive"},
                         {Region::kPrePostponed, "pre_postponed"});
}

TEST(SimCh45, ReactiveRestartsActiveSetBeforePrePostponed) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() {
    order.push_back("reactive");
    auto* new_active = sched.GetEventPool().Acquire();
    new_active->callback = [&]() { order.push_back("active_from_reactive"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, new_active);
  };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  auto* pre_postponed = sched.GetEventPool().Acquire();
  pre_postponed->callback = [&]() { order.push_back("pre_postponed"); };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pre_postponed);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "reactive");
  EXPECT_EQ(order[1], "active_from_reactive");
  EXPECT_EQ(order[2], "pre_postponed");
}

TEST(SimCh45, ExecuteRegionDrainsAllEventsInFIFOOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() { order.push_back(i); };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(order.size(), 5u);
  for (int i = 0; i < 5; ++i) {
    EXPECT_EQ(order[i], i);
  }
}

TEST(SimCh45, IterativeRegionOrderMatchesAlgorithm) {
  constexpr Region kIterativeRegions[] = {
      Region::kActive,     Region::kInactive,     Region::kPreNBA,
      Region::kNBA,        Region::kPostNBA,      Region::kPreObserved,
      Region::kObserved,   Region::kPostObserved, Region::kReactive,
      Region::kReInactive, Region::kPreReNBA,     Region::kReNBA,
      Region::kPostReNBA,  Region::kPrePostponed,
  };
  constexpr size_t kCount = sizeof(kIterativeRegions) / sizeof(Region);
  EXPECT_EQ(kCount, 14u);

  for (size_t i = 1; i < kCount; ++i) {
    auto prev = static_cast<int>(kIterativeRegions[i - 1]);
    auto curr = static_cast<int>(kIterativeRegions[i]);
    EXPECT_EQ(curr, prev + 1) << "Region ordinal gap at index " << i;
  }
}

TEST(Scheduler, InitialState) {
  Arena arena;
  Scheduler sched(arena);
  EXPECT_FALSE(sched.HasEvents());
  EXPECT_EQ(sched.CurrentTime().ticks, 0);
}

}  // namespace
