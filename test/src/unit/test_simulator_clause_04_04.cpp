#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(StratifiedEventSchedulerSim,
     SchedulerScheduledExecutedAndRemovedEventsThroughDataStructure) {
  Arena arena;
  Scheduler sched(arena);
  EXPECT_EQ(sched.GetEventPool().FreeCount(), 0u);

  int executed = 0;
  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&executed]() { ++executed; };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }
  EXPECT_TRUE(sched.HasEvents());

  sched.Run();
  EXPECT_EQ(executed, 5);
  EXPECT_FALSE(sched.HasEvents());
  EXPECT_EQ(sched.GetEventPool().FreeCount(), 5u);
}

TEST(StratifiedEventSchedulerSim,
     EventExecutesAtItsOneSimulationExecutionTime) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> fired_at;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { fired_at.push_back(sched.CurrentTime().ticks); };
  sched.ScheduleEvent({7}, Region::kActive, ev);

  sched.Run();
  ASSERT_EQ(fired_at.size(), 1u);
  EXPECT_EQ(fired_at[0], 7u);
}

TEST(StratifiedEventSchedulerSim, EventCanBeScheduledAtCurrentOrFutureTime) {
  Arena arena;
  Scheduler sched(arena);
  bool seeded_current = false;
  bool seeded_future = false;

  auto* seed = sched.GetEventPool().Acquire();
  seed->callback = [&]() {
    auto* now_event = sched.GetEventPool().Acquire();
    now_event->callback = [&]() { seeded_current = true; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kInactive, now_event);

    auto* future_event = sched.GetEventPool().Acquire();
    future_event->callback = [&]() { seeded_future = true; };
    sched.ScheduleEvent({sched.CurrentTime().ticks + 3}, Region::kActive,
                        future_event);
  };
  sched.ScheduleEvent({0}, Region::kActive, seed);

  sched.Run();
  EXPECT_TRUE(seeded_current);
  EXPECT_TRUE(seeded_future);
}

TEST(StratifiedEventSchedulerSim, EventsAtSameTimeShareASingleTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (int i = 0; i < 3; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { times.push_back(sched.CurrentTime().ticks); };
    sched.ScheduleEvent({4}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 4u);
  EXPECT_EQ(times[1], 4u);
  EXPECT_EQ(times[2], 4u);
}

TEST(StratifiedEventSchedulerSim,
     CurrentTimeSlotFullyExecutedBeforeAdvancingToNext) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> sequence;

  auto* a0 = sched.GetEventPool().Acquire();
  a0->callback = [&]() { sequence.push_back(sched.CurrentTime().ticks); };
  sched.ScheduleEvent({0}, Region::kActive, a0);

  auto* nba0 = sched.GetEventPool().Acquire();
  nba0->callback = [&]() { sequence.push_back(sched.CurrentTime().ticks); };
  sched.ScheduleEvent({0}, Region::kNBA, nba0);

  auto* a1 = sched.GetEventPool().Acquire();
  a1->callback = [&]() { sequence.push_back(sched.CurrentTime().ticks); };
  sched.ScheduleEvent({1}, Region::kActive, a1);

  sched.Run();
  ASSERT_EQ(sequence.size(), 3u);
  EXPECT_EQ(sequence[0], 0u);
  EXPECT_EQ(sequence[1], 0u);
  EXPECT_EQ(sequence[2], 1u);
}

TEST(StratifiedEventSchedulerSim, NextNonemptyTimeSlotIsExecutedInTimeOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t : {17u, 3u, 99u, 0u}) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { times.push_back(sched.CurrentTime().ticks); };
    sched.ScheduleEvent({t}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 4u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 3u);
  EXPECT_EQ(times[2], 17u);
  EXPECT_EQ(times[3], 99u);
}

TEST(StratifiedEventSchedulerSim,
     TimeSlotIsDividedIntoSeventeenOrderedRegionsPerLrmList) {
  EXPECT_EQ(kRegionCount, 17u);

  Arena arena;
  Scheduler sched(arena);
  std::vector<Region> fired;

  std::vector<Region> all_regions = {
      Region::kPostponed,   Region::kPrePostponed, Region::kPostReNBA,
      Region::kReNBA,       Region::kPreReNBA,     Region::kReInactive,
      Region::kReactive,    Region::kPostObserved, Region::kObserved,
      Region::kPreObserved, Region::kPostNBA,      Region::kNBA,
      Region::kPreNBA,      Region::kInactive,     Region::kActive,
      Region::kPreActive,   Region::kPreponed};
  for (Region r : all_regions) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&fired, r]() { fired.push_back(r); };
    sched.ScheduleEvent({0}, r, ev);
  }

  sched.Run();
  std::vector<Region> expected = {
      Region::kPreponed,     Region::kPreActive,   Region::kActive,
      Region::kInactive,     Region::kPreNBA,      Region::kNBA,
      Region::kPostNBA,      Region::kPreObserved, Region::kObserved,
      Region::kPostObserved, Region::kReactive,    Region::kReInactive,
      Region::kPreReNBA,     Region::kReNBA,       Region::kPostReNBA,
      Region::kPrePostponed, Region::kPostponed};
  EXPECT_EQ(fired, expected);
}

TEST(StratifiedEventSchedulerSimDeathTest,
     SchedulingAtPastTimeAbortsToPreventBackwardsInTime) {
  EXPECT_DEATH(
      {
        Arena arena;
        Scheduler sched(arena);
        auto* future = sched.GetEventPool().Acquire();
        future->callback = [&]() {
          auto* past = sched.GetEventPool().Acquire();
          past->callback = []() {};
          sched.ScheduleEvent({50}, Region::kActive, past);
        };
        sched.ScheduleEvent({100}, Region::kActive, future);
        sched.Run();
      },
      "backwards-in-time");
}
