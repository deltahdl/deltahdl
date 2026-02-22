#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.5 SystemVerilog simulation reference algorithm
//
// LRM §4.5 specifies three pseudocode functions:
//
//   execute_simulation:
//     T = 0; initialize all nets/variables; schedule initialization events
//     into time zero; advance through nonempty time slots in order.
//
//   execute_time_slot:
//     Preponed -> Pre-Active -> iterative {Active set -> Reactive set ->
//     Pre-Postponed} -> Postponed
//
//   execute_region:
//     While region is nonempty, remove event, dispatch (update or eval).
//
// The iterative regions are: Active, Inactive, Pre-NBA, NBA, Post-NBA,
// Pre-Observed, Observed, Post-Observed, Reactive, Re-Inactive, Pre-Re-NBA,
// Re-NBA, Post-Re-NBA, and Pre-Postponed.
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.5 execute_simulation: "T = 0"
// Simulation time starts at 0 and advances through nonempty time slots.
// ---------------------------------------------------------------------------
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

// ---------------------------------------------------------------------------
// §4.5 execute_simulation: "while (some time slot is nonempty) { move to the
// first nonempty time slot and set T; execute_time_slot(T); }"
// Time advances through nonempty slots in order, skipping empty ones.
// ---------------------------------------------------------------------------
TEST(SimCh45, ExecuteSimulationAdvancesThroughNonemptyTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  // Schedule at times 0, 5, 10 — gaps at 1-4 and 6-9 must be skipped.
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

// ---------------------------------------------------------------------------
// §4.5 execute_simulation: simulation stops when all time slots are empty.
// ---------------------------------------------------------------------------
TEST(SimCh45, ExecuteSimulationStopsWhenAllTimeSlotsEmpty) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { count++; };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  EXPECT_EQ(count, 1);
  // After Run(), no more events — HasEvents() should be false.
  EXPECT_FALSE(sched.HasEvents());
}

// ---------------------------------------------------------------------------
// §4.5 execute_time_slot: full region chain ordering.
// Preponed -> Pre-Active -> Active set -> Reactive set -> Postponed.
// ---------------------------------------------------------------------------
TEST(SimCh45, ExecuteTimeSlotFullRegionOrdering) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule in reverse to prove ordering.
  schedule(Region::kPostponed, "postponed");
  schedule(Region::kPrePostponed, "pre_postponed");
  schedule(Region::kPostReNBA, "post_re_nba");
  schedule(Region::kReNBA, "re_nba");
  schedule(Region::kPreReNBA, "pre_re_nba");
  schedule(Region::kReInactive, "re_inactive");
  schedule(Region::kReactive, "reactive");
  schedule(Region::kPostObserved, "post_observed");
  schedule(Region::kObserved, "observed");
  schedule(Region::kPreObserved, "pre_observed");
  schedule(Region::kPostNBA, "post_nba");
  schedule(Region::kNBA, "nba");
  schedule(Region::kPreNBA, "pre_nba");
  schedule(Region::kInactive, "inactive");
  schedule(Region::kActive, "active");
  schedule(Region::kPreActive, "pre_active");
  schedule(Region::kPreponed, "preponed");

  sched.Run();
  std::vector<std::string> expected = {
      "preponed",   "pre_active",    "active",      "inactive",
      "pre_nba",    "nba",           "post_nba",    "pre_observed",
      "observed",   "post_observed", "reactive",    "re_inactive",
      "pre_re_nba", "re_nba",        "post_re_nba", "pre_postponed",
      "postponed"};
  EXPECT_EQ(order, expected);
}

// ---------------------------------------------------------------------------
// §4.5 Active set iteration: "execute_region (Active); R = first nonempty
// region in [Active ... Post-Observed]; if (R is nonempty) move events in R
// to the Active region;"
// An Inactive callback that generates Active events: Active re-executes.
// ---------------------------------------------------------------------------
TEST(SimCh45, ActiveSetIterationReExecutesActiveAfterInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Inactive callback schedules a new Active event.
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

// ---------------------------------------------------------------------------
// §4.5 Active set iteration: NBA generates Active event -> re-iterates.
// An NBA callback schedules an Active event; Active set must re-iterate.
// ---------------------------------------------------------------------------
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
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Active, Reactive, and Pre-Postponed all scheduled.
  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kPrePostponed, "pre_postponed");
  schedule(Region::kReactive, "reactive");
  schedule(Region::kActive, "active");

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "reactive");
  EXPECT_EQ(order[2], "pre_postponed");
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
