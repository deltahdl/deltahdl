#include <gtest/gtest.h>

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

// §4.4.1 ¶3 partition assertions (sum, disjointness, coverage) live in
// test_simulator_clause_04_04_01.cpp; this file scopes simulation/PLI
// enumeration tests to §4.4.2.

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

// §4.4.2 ¶1 enumeration: production-code IsSimulationRegion classifies the
// nine LRM-named regions (Preponed, Active, Inactive, NBA, Observed, Reactive,
// Re-Inactive, Re-NBA, Postponed) as simulation regions and rejects every
// other region. The §4.4.1 partition tests assert sum/disjointness/coverage
// but do not pin classifier membership to the §4.4.2 enumeration.
TEST(SimAndPliRegionSim, IsSimulationRegionMatchesEnumeration) {
  for (auto r : kSimulationRegions) {
    EXPECT_TRUE(IsSimulationRegion(r))
        << "expected simulation region index " << static_cast<int>(r);
  }
  for (auto r : kPLIRegions) {
    EXPECT_FALSE(IsSimulationRegion(r))
        << "unexpected simulation region index " << static_cast<int>(r);
  }
  size_t sim_count = 0;
  for (size_t i = 0; i < kRegionCount; ++i) {
    if (IsSimulationRegion(static_cast<Region>(i))) ++sim_count;
  }
  EXPECT_EQ(sim_count, kSimulationRegionCount);
}
