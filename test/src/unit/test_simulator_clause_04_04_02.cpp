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

// §4.4.2 ¶1 sentence 2: "The flow of execution of the event regions is
// specified in Figure 4-1." Figure 4-1 is a per-time-slot flow; sequential
// slots must each apply it independently. Run() drives Scheduler over the
// event_calendar map; observing the cross-slot trace shows production code
// re-entering the per-slot region order at every slot rather than collapsing
// regions across slots. Two slots with sim-region events at each prove the
// flow re-applies: time 0's Active must precede time 0's Postponed, time 1's
// Active must precede time 1's Postponed, and time 0's Postponed must precede
// time 1's Active (since slots advance in time order per §4.4 ¶2 and the slot
// flow does not bleed across slots).
TEST(SimAndPliRegionSim, SimulationRegionFlowAppliesPerTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  for (uint64_t t = 0; t < 2; ++t) {
    auto* postponed = sched.GetEventPool().Acquire();
    postponed->callback = [&order, t]() {
      order.push_back("postponed@" + std::to_string(t));
    };
    sched.ScheduleEvent({t}, Region::kPostponed, postponed);

    auto* active = sched.GetEventPool().Acquire();
    active->callback = [&order, t]() {
      order.push_back("active@" + std::to_string(t));
    };
    sched.ScheduleEvent({t}, Region::kActive, active);
  }

  sched.Run();
  std::vector<std::string> expected = {"active@0", "postponed@0", "active@1",
                                       "postponed@1"};
  EXPECT_EQ(order, expected);
}

// §4.4.2 ¶1 sentence 2: Figure 4-1's flow must hold even when most regions in
// a slot are empty. Production Scheduler::ExecuteTimeSlot walks the regions
// in fixed enum order, draining each queue (which is a no-op when empty), so
// the listed simulation regions still execute in their Figure 4-1 order
// regardless of which neighbours have events. Edge case: only Preponed and
// Postponed are populated — they are the slot's first and last simulation
// regions, so the relative order is the strongest pin.
TEST(SimAndPliRegionSim, SparselyPopulatedSimulationRegionsExecuteInOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&order]() { order.push_back("postponed"); };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&order]() { order.push_back("preponed"); };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "preponed");
  EXPECT_EQ(order[1], "postponed");
}
