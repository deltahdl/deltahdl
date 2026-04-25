#include <gtest/gtest.h>

#include <set>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

namespace {

constexpr Region kSimulationRegions[] = {
    Region::kPreponed,   Region::kActive,   Region::kInactive,
    Region::kNBA,        Region::kObserved, Region::kReactive,
    Region::kReInactive, Region::kReNBA,    Region::kPostponed,
};

constexpr size_t kSimulationRegionCount = 9;

constexpr Region kPLIRegions[] = {
    Region::kPreActive,   Region::kPreNBA,       Region::kPostNBA,
    Region::kPreObserved, Region::kPostObserved, Region::kPreReNBA,
    Region::kPostReNBA,   Region::kPrePostponed,
};

constexpr size_t kPLIRegionCount = 8;

}  // namespace

TEST(SimAndPliRegionSim, SimulationRegionCountIs9) {
  EXPECT_EQ(kSimulationRegionCount, 9u);
  EXPECT_EQ(sizeof(kSimulationRegions) / sizeof(kSimulationRegions[0]), 9u);
}

TEST(SimAndPliRegionSim, PLIRegionCountIs8) {
  EXPECT_EQ(kPLIRegionCount, 8u);
  EXPECT_EQ(sizeof(kPLIRegions) / sizeof(kPLIRegions[0]), 8u);
}

TEST(SimAndPliRegionSim, SimPlusPLIEqualsTotal) {
  EXPECT_EQ(kSimulationRegionCount + kPLIRegionCount, kRegionCount);
}

TEST(SimAndPliRegionSim, SimAndPLIAreDisjoint) {
  std::set<Region> sim_set(std::begin(kSimulationRegions),
                           std::end(kSimulationRegions));
  std::set<Region> pli_set(std::begin(kPLIRegions), std::end(kPLIRegions));

  for (auto r : pli_set) {
    EXPECT_EQ(sim_set.count(r), 0u);
  }
}

TEST(SimAndPliRegionSim, SimAndPLICoverAllRegions) {
  std::set<Region> all;
  for (auto r : kSimulationRegions) all.insert(r);
  for (auto r : kPLIRegions) all.insert(r);
  EXPECT_EQ(all.size(), kRegionCount);
}

TEST(SimAndPliRegionSim, AllPLIRegionsExecute) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (auto r : kPLIRegions) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&count]() { count++; };
    sched.ScheduleEvent({0}, r, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 8);
}

TEST(SimAndPliRegionSim, SimulationRegionsExecuteInOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  for (size_t i = 0; i < kSimulationRegionCount; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    int id = static_cast<int>(i);
    ev->callback = [&order, id]() { order.push_back(id); };
    sched.ScheduleEvent({0}, kSimulationRegions[i], ev);
  }

  sched.Run();
  ASSERT_EQ(order.size(), kSimulationRegionCount);
  for (size_t i = 0; i < kSimulationRegionCount; ++i) {
    EXPECT_EQ(order[i], static_cast<int>(i));
  }
}

TEST(SimAndPliRegionSim, PreponedIsFirstPostponedIsLast) {
  EXPECT_EQ(static_cast<int>(Region::kPreponed), 0);
  EXPECT_EQ(static_cast<int>(Region::kPostponed),
            static_cast<int>(Region::kCOUNT) - 1);
}

TEST(SimAndPliRegionSim, MixedSimAndPLIRegionsExecuteInOrder) {
  VerifyAllRegionsExecuteInOrder();
}
