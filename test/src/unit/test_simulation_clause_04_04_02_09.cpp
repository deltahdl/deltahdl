#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.2.9 Postponed events region
//
// Figure 4-1 shows:
//   pli_region_PrePostponed -> region_Postponed  (forward from PrePostponed)
//   region_Postponed -> NextSlot                  (terminal -- next time slot)
//
// The Postponed region is the last simulation region in a time slot.
// It is NOT part of the iterative region set (§4.4.1).
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.2.9 Postponed region event execution
// Basic: events scheduled in the Postponed region are executed.
// ---------------------------------------------------------------------------
TEST(SimCh4429, PostponedRegionExecutesEvents) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kPostponed, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

// ---------------------------------------------------------------------------
// §4.4.2.9 Postponed region holds multiple events
// Multiple monitor/strobe-like events coexist and all execute.
// ---------------------------------------------------------------------------
TEST(SimCh4429, PostponedRegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPostponed, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

// ---------------------------------------------------------------------------
// §4.4.2.9 Postponed observes final state
// Postponed callbacks observe the final state of all prior regions --
// values set in Active, NBA, Reactive, and Re-NBA are all visible.
// ---------------------------------------------------------------------------
TEST(SimCh4429, PostponedObservesFinalState) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  // Active at time 0 sets value = 10.
  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { value = 10; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  // NBA at time 0 sets value = 20.
  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { value = 20; };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  // Reactive at time 0 sets value = 30.
  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() { value = 30; };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  // Re-NBA at time 0 sets value = 40.
  auto* renba = sched.GetEventPool().Acquire();
  renba->callback = [&]() { value = 40; };
  sched.ScheduleEvent({0}, Region::kReNBA, renba);

  // Postponed samples value — should see final state (40).
  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  EXPECT_EQ(sampled, 40);
}

// ---------------------------------------------------------------------------
// §4.4.2.9 Postponed executes after ALL other simulation regions.
// Full region ordering: Active < Inactive < NBA < Observed < Reactive <
// ReInactive < ReNBA < Postponed.
// ---------------------------------------------------------------------------
TEST(SimCh4429, PostponedExecutesAfterAllOtherSimulationRegions) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule in reverse order to prove region ordering, not insertion order.
  schedule(Region::kPostponed, "postponed");
  schedule(Region::kReNBA, "renba");
  schedule(Region::kReInactive, "reinactive");
  schedule(Region::kReactive, "reactive");
  schedule(Region::kObserved, "observed");
  schedule(Region::kNBA, "nba");
  schedule(Region::kInactive, "inactive");
  schedule(Region::kActive, "active");

  sched.Run();
  ASSERT_EQ(order.size(), 8u);
  EXPECT_EQ(order[7], "postponed");
}

// ---------------------------------------------------------------------------
// §4.4.2.9 Postponed is the last region (ordinal 16) — after PrePostponed.
// Figure 4-1: pli_region_PrePostponed -> region_Postponed -> NextSlot.
// ---------------------------------------------------------------------------
TEST(SimCh4429, PostponedIsLastRegionOrdinal) {
  auto postponed_ord = static_cast<int>(Region::kPostponed);
  auto pre_postponed_ord = static_cast<int>(Region::kPrePostponed);
  auto count_ord = static_cast<int>(Region::kCOUNT);
  EXPECT_GT(postponed_ord, pre_postponed_ord);
  EXPECT_EQ(postponed_ord + 1, count_ord);
}

// ---------------------------------------------------------------------------
// §4.4.2.9 Postponed is NOT part of the iterative region set (§4.4.1).
// Once Postponed executes, it does not re-execute even if Active-set or
// Reactive-set iteration occurred earlier in the time slot.
// ---------------------------------------------------------------------------
TEST(SimCh4429, PostponedDoesNotReExecuteDuringIteration) {
  Arena arena;
  Scheduler sched(arena);
  int postponed_count = 0;

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { postponed_count++; };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  // Active callback triggers NBA (causing active-set re-iteration).
  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    auto* nba = sched.GetEventPool().Acquire();
    nba->callback = [&]() {
      // NBA schedules new Active -> triggers re-iteration.
      auto* act2 = sched.GetEventPool().Acquire();
      act2->callback = []() {};
      sched.ScheduleEvent({0}, Region::kActive, act2);
    };
    sched.ScheduleEvent({0}, Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  EXPECT_EQ(postponed_count, 1);
}

// ---------------------------------------------------------------------------
// §4.4.2.9 Figure 4-1: region_Postponed -> NextSlot.
// Postponed at time T completes before Preponed at time T+1.
// This is the terminal edge — Postponed advances to the next time slot.
// ---------------------------------------------------------------------------
TEST(SimCh4429, PostponedAdvancesToNextTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Postponed at time 0.
  auto* postponed0 = sched.GetEventPool().Acquire();
  postponed0->callback = [&]() { order.push_back("postponed_t0"); };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed0);

  // Preponed at time 1 — runs after Postponed at time 0.
  auto* preponed1 = sched.GetEventPool().Acquire();
  preponed1->callback = [&]() { order.push_back("preponed_t1"); };
  sched.ScheduleEvent({1}, Region::kPreponed, preponed1);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "postponed_t0");
  EXPECT_EQ(order[1], "preponed_t1");
}

// ---------------------------------------------------------------------------
// §4.4.2.9 Postponed PLI events
// PLI events and simulation events both execute in the Postponed queue --
// the scheduler makes no distinction.
// ---------------------------------------------------------------------------
TEST(SimCh4429, PostponedPLIEventsExecuteInRegion) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Simulate a "PLI" event and a "simulation" event both in Postponed.
  auto* pli_ev = sched.GetEventPool().Acquire();
  pli_ev->callback = [&order]() { order.push_back("pli"); };
  sched.ScheduleEvent({0}, Region::kPostponed, pli_ev);

  auto* sim_ev = sched.GetEventPool().Acquire();
  sim_ev->callback = [&order]() { order.push_back("sim"); };
  sched.ScheduleEvent({0}, Region::kPostponed, sim_ev);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pli");
  EXPECT_EQ(order[1], "sim");
}

// ---------------------------------------------------------------------------
// §4.4.2.9 Postponed events across multiple time slots.
// Each time slot has its own Postponed region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh4429, PostponedEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPostponed, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

// ---------------------------------------------------------------------------
// §4.4.2.9 Postponed state persists to next Preponed (cross-ref §4.4.2.1)
// This cross-reference test verifies that Postponed at time T and Preponed
// at time T+1 observe the same shared state.
// ---------------------------------------------------------------------------
TEST(SimCh4429, PostponedStatePersistsToNextPreponed) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled_postponed = -1;
  int sampled_preponed = -1;

  // Active at time 0 sets value = 100.
  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { value = 100; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  // Postponed at time 0 samples value.
  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { sampled_postponed = value; };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  // Preponed at time 1 samples value (should match Postponed at time 0).
  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { sampled_preponed = value; };
  sched.ScheduleEvent({1}, Region::kPreponed, preponed);

  // Active at time 1 modifies value — but Preponed already ran.
  auto* active1 = sched.GetEventPool().Acquire();
  active1->callback = [&]() { value = 999; };
  sched.ScheduleEvent({1}, Region::kActive, active1);

  sched.Run();
  EXPECT_EQ(sampled_postponed, 100);
  EXPECT_EQ(sampled_preponed, 100);
}
