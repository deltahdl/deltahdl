// Non-LRM tests

#include <gtest/gtest.h>
#include <string>
#include <vector>
#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// §4.5 execute_region: "while (region is nonempty) { E = any event from
// region; remove E from the region; ... }"
// Multiple events in a single region all execute (FIFO order).
// ---------------------------------------------------------------------------
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

// ---------------------------------------------------------------------------
// §4.5 "The Iterative regions and their order are Active, Inactive, Pre-NBA,
// NBA, Post-NBA, Pre-Observed, Observed, Post-Observed, Reactive,
// Re-Inactive, Pre-Re-NBA, Re-NBA, Post-Re-NBA, and Pre-Postponed."
// Verify these 14 regions are contiguous and in the correct order.
// ---------------------------------------------------------------------------
TEST(SimCh45, IterativeRegionOrderMatchesAlgorithm) {
  // The 14 iterative regions per §4.5.
  constexpr Region kIterativeRegions[] = {
      Region::kActive,     Region::kInactive,     Region::kPreNBA,
      Region::kNBA,        Region::kPostNBA,      Region::kPreObserved,
      Region::kObserved,   Region::kPostObserved, Region::kReactive,
      Region::kReInactive, Region::kPreReNBA,     Region::kReNBA,
      Region::kPostReNBA,  Region::kPrePostponed,
  };
  constexpr size_t kCount = sizeof(kIterativeRegions) / sizeof(Region);
  EXPECT_EQ(kCount, 14u);

  // Each ordinal must be exactly 1 greater than the previous.
  for (size_t i = 1; i < kCount; ++i) {
    auto prev = static_cast<int>(kIterativeRegions[i - 1]);
    auto curr = static_cast<int>(kIterativeRegions[i]);
    EXPECT_EQ(curr, prev + 1) << "Region ordinal gap at index " << i;
  }
}

}  // namespace
