#include <gtest/gtest.h>

#include <set>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(ActiveRegionSim, ActiveRegionEventsAllProcessedRegardlessOfOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> observed;

  constexpr int kN = 5;
  for (int i = 0; i < kN; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&observed, i]() { observed.push_back(i); };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(observed.size(), static_cast<size_t>(kN));
  std::set<int> seen(observed.begin(), observed.end());
  EXPECT_EQ(seen.size(), static_cast<size_t>(kN));
  for (int i = 0; i < kN; ++i) {
    EXPECT_TRUE(seen.count(i)) << "missing Active event id " << i;
  }
}

TEST(ActiveRegionSim, CurrentRegionIsActiveDuringActiveEventEvaluation) {
  Arena arena;
  Scheduler sched(arena);
  Region observed = Region::kCOUNT;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { observed = sched.CurrentRegion(); };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  EXPECT_EQ(observed, Region::kActive);
}

TEST(ActiveRegionSim, ActiveRegionEmptyDoesNotBlockOtherRegions) {
  Arena arena;
  Scheduler sched(arena);
  bool inactive_fired = false;
  bool postponed_fired = false;

  auto* inactive = sched.GetEventPool().Acquire();
  inactive->callback = [&]() { inactive_fired = true; };
  sched.ScheduleEvent({0}, Region::kInactive, inactive);

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { postponed_fired = true; };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  EXPECT_TRUE(inactive_fired);
  EXPECT_TRUE(postponed_fired);
}

TEST(ActiveRegionSim, ActiveRegionHoldsEventsScheduledDuringActiveEvaluation) {
  Arena arena;
  Scheduler sched(arena);
  bool outer_fired = false;
  bool inner_fired = false;

  auto* outer = sched.GetEventPool().Acquire();
  outer->callback = [&]() {
    outer_fired = true;
    auto* inner = sched.GetEventPool().Acquire();
    inner->callback = [&]() { inner_fired = true; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, inner);
  };
  sched.ScheduleEvent({0}, Region::kActive, outer);

  sched.Run();
  EXPECT_TRUE(outer_fired);
  EXPECT_TRUE(inner_fired);
}
