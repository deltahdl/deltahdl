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
// §4.5 Reactive set iteration: "execute_region (Reactive); R = first nonempty
// region in [Reactive ... Post-Re-NBA]; if (R is nonempty) move events in R
// to the Reactive region;"
// Re-Inactive generates Reactive event -> Reactive re-executes.
// ---------------------------------------------------------------------------
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

// ---------------------------------------------------------------------------
// §4.5 "if (all regions in [Active ... Post-Re-NBA] are empty)
//        execute_region (Pre-Postponed);"
// Pre-Postponed only fires after Active and Reactive sets are fully drained.
// ---------------------------------------------------------------------------
TEST(SimCh45, PrePostponedOnlyAfterActiveAndReactiveSetsEmpty) {
  VerifyThreeRegionOrder(Region::kActive, "active", Region::kReactive,
                         "reactive", Region::kPrePostponed, "pre_postponed");
}

// ---------------------------------------------------------------------------
// §4.5 Outer loop: Reactive region schedules Active event -> active set
// re-processes before Pre-Postponed can fire.
// ---------------------------------------------------------------------------
TEST(SimCh45, ReactiveRestartsActiveSetBeforePrePostponed) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Reactive generates an Active event.
  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() {
    order.push_back("reactive");
    auto* new_active = sched.GetEventPool().Acquire();
    new_active->callback = [&]() { order.push_back("active_from_reactive"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, new_active);
  };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  // Pre-Postponed must wait until both active and reactive are fully drained.
  auto* pre_postponed = sched.GetEventPool().Acquire();
  pre_postponed->callback = [&]() { order.push_back("pre_postponed"); };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pre_postponed);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "reactive");
  EXPECT_EQ(order[1], "active_from_reactive");
  EXPECT_EQ(order[2], "pre_postponed");
}

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
