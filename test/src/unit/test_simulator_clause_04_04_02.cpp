#include <gtest/gtest.h>

#include <set>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.2 Simulation regions
//
// LRM §4.4.2: "The simulation regions of a time slot are the Preponed,
// Active, Inactive, NBA, Observed, Reactive, Re-Inactive, Re-NBA and
// Postponed regions. The flow of execution of the event regions is
// specified in Figure 4-1."
//
// This identifies exactly 9 simulation regions (as opposed to 8 PLI
// regions from §4.4.3).  Together, 9 + 8 = 17 = kRegionCount.
// ===========================================================================

namespace {

// The 9 simulation regions per §4.4.2.
constexpr Region kSimulationRegions[] = {
    Region::kPreponed,   Region::kActive,   Region::kInactive,
    Region::kNBA,        Region::kObserved, Region::kReactive,
    Region::kReInactive, Region::kReNBA,    Region::kPostponed,
};

constexpr size_t kSimulationRegionCount = 9;

// The 8 PLI regions per §4.4.3 (complement of simulation regions).
constexpr Region kPLIRegions[] = {
    Region::kPreActive,   Region::kPreNBA,       Region::kPostNBA,
    Region::kPreObserved, Region::kPostObserved, Region::kPreReNBA,
    Region::kPostReNBA,   Region::kPrePostponed,
};

constexpr size_t kPLIRegionCount = 8;

}  // namespace

// ---------------------------------------------------------------------------
// §4.4.2 Simulation regions are exactly 9.
// ---------------------------------------------------------------------------
TEST(SimCh442, SimulationRegionCountIs9) {
  EXPECT_EQ(kSimulationRegionCount, 9u);
  EXPECT_EQ(sizeof(kSimulationRegions) / sizeof(kSimulationRegions[0]), 9u);
}

// ---------------------------------------------------------------------------
// §4.4.2 PLI regions are exactly 8 (complement of simulation regions).
// ---------------------------------------------------------------------------
TEST(SimCh442, PLIRegionCountIs8) {
  EXPECT_EQ(kPLIRegionCount, 8u);
  EXPECT_EQ(sizeof(kPLIRegions) / sizeof(kPLIRegions[0]), 8u);
}

// ---------------------------------------------------------------------------
// §4.4.2 Simulation regions + PLI regions = kRegionCount (17).
// This proves the two categories are an exhaustive partition.
// ---------------------------------------------------------------------------
TEST(SimCh442, SimPlusPLIEqualsTotal) {
  EXPECT_EQ(kSimulationRegionCount + kPLIRegionCount, kRegionCount);
}

// ---------------------------------------------------------------------------
// §4.4.2 Simulation regions and PLI regions are disjoint — no overlap.
// ---------------------------------------------------------------------------
TEST(SimCh442, SimAndPLIAreDisjoint) {
  std::set<Region> sim_set(std::begin(kSimulationRegions),
                           std::end(kSimulationRegions));
  std::set<Region> pli_set(std::begin(kPLIRegions), std::end(kPLIRegions));

  for (auto r : pli_set) {
    EXPECT_EQ(sim_set.count(r), 0u);
  }
}

// ---------------------------------------------------------------------------
// §4.4.2 Simulation + PLI regions cover all 17 regions.
// ---------------------------------------------------------------------------
TEST(SimCh442, SimAndPLICoverAllRegions) {
  std::set<Region> all;
  for (auto r : kSimulationRegions) all.insert(r);
  for (auto r : kPLIRegions) all.insert(r);
  EXPECT_EQ(all.size(), kRegionCount);
}

// ---------------------------------------------------------------------------
// §4.4.2 All 9 simulation regions execute within a single time slot.
// ---------------------------------------------------------------------------
TEST(SimCh442, AllSimulationRegionsExecute) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (auto r : kSimulationRegions) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&count]() { count++; };
    sched.ScheduleEvent({0}, r, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 9);
}

// ---------------------------------------------------------------------------
// §4.4.2 All 8 PLI regions also execute within a single time slot.
// This confirms PLI regions participate in execution even though they
// are not "simulation regions" per §4.4.2.
// ---------------------------------------------------------------------------
TEST(SimCh442, AllPLIRegionsExecute) {
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

// ---------------------------------------------------------------------------
// §4.4.2 "The flow of execution of the event regions is specified in
// Figure 4-1."  The simulation regions execute in the canonical order:
// Preponed < Active < Inactive < NBA < Observed < Reactive <
// Re-Inactive < Re-NBA < Postponed.
// ---------------------------------------------------------------------------
TEST(SimCh442, SimulationRegionsExecuteInOrder) {
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

// ---------------------------------------------------------------------------
// §4.4.2 Simulation regions span the full time slot from Preponed (first)
// to Postponed (last).  Preponed is ordinal 0 and Postponed is the last
// before kCOUNT.
// ---------------------------------------------------------------------------
TEST(SimCh442, PreponedIsFirstPostponedIsLast) {
  EXPECT_EQ(static_cast<int>(Region::kPreponed), 0);
  EXPECT_EQ(static_cast<int>(Region::kPostponed),
            static_cast<int>(Region::kCOUNT) - 1);
}

// ---------------------------------------------------------------------------
// §4.4.2 PLI regions interleave with simulation regions but do not change
// their relative order.  A mixed schedule of simulation and PLI regions
// should execute all events respecting the region ordering.
// ---------------------------------------------------------------------------
TEST(SimCh442, MixedSimAndPLIRegionsExecuteInOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  // Schedule one event in every region.
  for (int r = 0; r < static_cast<int>(Region::kCOUNT); ++r) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, r]() { order.push_back(r); };
    sched.ScheduleEvent({0}, static_cast<Region>(r), ev);
  }

  sched.Run();
  ASSERT_EQ(order.size(), kRegionCount);

  // Verify monotonically increasing region ordinals.
  for (size_t i = 1; i < order.size(); ++i) {
    EXPECT_GT(order[i], order[i - 1]);
  }
}
