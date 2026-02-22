#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.2.1 Preponed events region
//
// Figure 4-1 shows: PrevSlot -> Preponed -> PreActive -> Active -> ...
// Preponed is the very first region in every time slot and has no
// feedback edges into it -- it executes exactly once per time slot.
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.2.1 Preponed executes before all other regions in the time slot.
// Verifies that Preponed runs before Active.
// ---------------------------------------------------------------------------
TEST(SimCh4421, PreponedExecutesBeforeAllOtherRegions) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule in reverse order to prove the scheduler orders by region.
  schedule(Region::kPostponed, "postponed");
  schedule(Region::kReactive, "reactive");
  schedule(Region::kObserved, "observed");
  schedule(Region::kNBA, "nba");
  schedule(Region::kActive, "active");
  schedule(Region::kPreponed, "preponed");

  sched.Run();
  ASSERT_GE(order.size(), 1u);
  EXPECT_EQ(order[0], "preponed");
}

// ---------------------------------------------------------------------------
// §4.4.2.1 #1step sampling via Preponed region
// A Preponed callback at time T samples a value before any Active
// modifications at time T.  The sampled value reflects the state from
// before the current time slot.
// ---------------------------------------------------------------------------
TEST(SimCh4421, PreponedSamplesBeforeActiveModifications) {
  Arena arena;
  Scheduler sched(arena);
  int shared_value = 0;
  int sampled_in_preponed = -1;
  int sampled_in_active = -1;

  // Active at time 0 sets shared_value = 42.
  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    shared_value = 42;
    sampled_in_active = shared_value;
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  // Preponed at time 0 samples shared_value before Active runs.
  auto* preponed = sched.GetEventPool().Acquire();
  preponed->callback = [&]() { sampled_in_preponed = shared_value; };
  sched.ScheduleEvent({0}, Region::kPreponed, preponed);

  sched.Run();
  EXPECT_EQ(sampled_in_preponed, 0);
  EXPECT_EQ(sampled_in_active, 42);
}

// ---------------------------------------------------------------------------
// §4.4.2.1 Preponed equivalent to previous Postponed
// A Postponed callback at time T-1 and a Preponed callback at time T
// observe the same shared state -- nothing changes between them.
// ---------------------------------------------------------------------------
TEST(SimCh4421, PreponedEquivalentToPreviousPostponed) {
  Arena arena;
  Scheduler sched(arena);
  int shared_value = 0;
  int sampled_in_postponed = -1;
  int sampled_in_preponed = -1;

  // Active at time 0 sets shared_value = 100.
  auto* active0 = sched.GetEventPool().Acquire();
  active0->callback = [&]() { shared_value = 100; };
  sched.ScheduleEvent({0}, Region::kActive, active0);

  // Postponed at time 0 samples shared_value after all time-0 activity.
  auto* postponed0 = sched.GetEventPool().Acquire();
  postponed0->callback = [&]() { sampled_in_postponed = shared_value; };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed0);

  // Preponed at time 1 samples shared_value before time-1 activity.
  auto* preponed1 = sched.GetEventPool().Acquire();
  preponed1->callback = [&]() { sampled_in_preponed = shared_value; };
  sched.ScheduleEvent({1}, Region::kPreponed, preponed1);

  // Active at time 1 modifies shared_value — but Preponed already ran.
  auto* active1 = sched.GetEventPool().Acquire();
  active1->callback = [&]() { shared_value = 999; };
  sched.ScheduleEvent({1}, Region::kActive, active1);

  sched.Run();
  EXPECT_EQ(sampled_in_postponed, 100);
  EXPECT_EQ(sampled_in_preponed, 100);
}

// ---------------------------------------------------------------------------
// §4.4.2.1 Preponed is not part of the iterative region set (per §4.4.1
// and Figure 4-1).  Once Preponed executes, it does not re-execute even
// if Active-set iteration occurs.
// ---------------------------------------------------------------------------
TEST(SimCh4421, PreponedDoesNotReExecuteDuringIteration) {
  Arena arena;
  Scheduler sched(arena);
  int preponed_count = 0;

  // Preponed callback counts executions.
  auto* prep = sched.GetEventPool().Acquire();
  prep->callback = [&]() { preponed_count++; };
  sched.ScheduleEvent({0}, Region::kPreponed, prep);

  // Active callback schedules an NBA (triggering active-set re-iteration).
  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    auto* nba = sched.GetEventPool().Acquire();
    nba->callback = []() {};
    sched.ScheduleEvent({0}, Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  EXPECT_EQ(preponed_count, 1);
}

// ---------------------------------------------------------------------------
// §4.4.2.1 Preponed PLI events
// PLI events and simulation events both execute in the Preponed queue --
// the scheduler makes no distinction.
// ---------------------------------------------------------------------------
TEST(SimCh4421, PreponedPLIEventsExecuteInRegion) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Simulate a "PLI" event and a "simulation" event both in Preponed.
  auto* pli_ev = sched.GetEventPool().Acquire();
  pli_ev->callback = [&order]() { order.push_back("pli"); };
  sched.ScheduleEvent({0}, Region::kPreponed, pli_ev);

  auto* sim_ev = sched.GetEventPool().Acquire();
  sim_ev->callback = [&order]() { order.push_back("sim"); };
  sched.ScheduleEvent({0}, Region::kPreponed, sim_ev);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pli");
  EXPECT_EQ(order[1], "sim");
}

// ---------------------------------------------------------------------------
// §4.4.2.1 Preponed runs exactly once per time slot, even across multiple
// time slots.  Each time slot gets its own Preponed execution.
// ---------------------------------------------------------------------------
TEST(SimCh4421, PreponedRunsOncePerTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  int preponed_count = 0;

  // Schedule Preponed events at 3 different times.
  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { preponed_count++; };
    sched.ScheduleEvent({t}, Region::kPreponed, ev);
  }

  sched.Run();
  EXPECT_EQ(preponed_count, 3);
}

// ---------------------------------------------------------------------------
// §4.4.2.1 The #1step delay concept: scheduling at the Preponed region
// of time T is the mechanism for #1step.  The sampled value at Preponed
// time T equals the value at end of time T-1 (not mid-timeslot T).
// ---------------------------------------------------------------------------
TEST(SimCh4421, OneStepDelayMechanismViaPreponedRegion) {
  Arena arena;
  Scheduler sched(arena);
  int value = 10;
  int one_step_sample = -1;

  // Time 0: Active sets value = 20, Postponed sees 20.
  auto* act0 = sched.GetEventPool().Acquire();
  act0->callback = [&]() { value = 20; };
  sched.ScheduleEvent({0}, Region::kActive, act0);

  // Time 1: Preponed (#1step sample) captures value before time-1 starts.
  auto* prep1 = sched.GetEventPool().Acquire();
  prep1->callback = [&]() { one_step_sample = value; };
  sched.ScheduleEvent({1}, Region::kPreponed, prep1);

  // Time 1: Active modifies value = 30 (after Preponed already sampled).
  auto* act1 = sched.GetEventPool().Acquire();
  act1->callback = [&]() { value = 30; };
  sched.ScheduleEvent({1}, Region::kActive, act1);

  sched.Run();
  EXPECT_EQ(one_step_sample, 20);
  EXPECT_EQ(value, 30);
}

// ---------------------------------------------------------------------------
// §4.4.2.1 Figure 4-1 shows Preponed has no incoming feedback edges.
// The only incoming edge is from "previous time slot".  This means
// even reactive-to-active restart cannot cause Preponed to re-execute.
// ---------------------------------------------------------------------------
TEST(SimCh4421, PreponedNotReExecutedByReactiveToActiveRestart) {
  Arena arena;
  Scheduler sched(arena);
  int preponed_count = 0;

  auto* prep = sched.GetEventPool().Acquire();
  prep->callback = [&]() { preponed_count++; };
  sched.ScheduleEvent({0}, Region::kPreponed, prep);

  // Reactive callback schedules an Active event (triggers restart).
  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() {
    auto* active2 = sched.GetEventPool().Acquire();
    active2->callback = []() {};
    sched.ScheduleEvent({0}, Region::kActive, active2);
  };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  sched.Run();
  EXPECT_EQ(preponed_count, 1);
}

// ---------------------------------------------------------------------------
// §4.4.2.1 Preponed is ordinal 0 in the Region enum — it is the very
// first region, confirming its position at the start of every time slot.
// ---------------------------------------------------------------------------
TEST(SimCh4421, PreponedIsOrdinalZero) {
  EXPECT_EQ(static_cast<int>(Region::kPreponed), 0);
}

// ---------------------------------------------------------------------------
// §4.4.2.1 Combined: Preponed at time T sees state from Postponed at
// time T-1 even when multiple time slots with modifications intervene.
// Three time slots: T=0, T=1, T=2.  Value updated at each Active.
// Preponed at each subsequent time sees previous Active's final value.
// ---------------------------------------------------------------------------
TEST(SimCh4421, PreponedSeesCorrectStateAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  std::vector<int> preponed_samples;

  // Time 0: Active sets value = 10.
  auto* act0 = sched.GetEventPool().Acquire();
  act0->callback = [&]() { value = 10; };
  sched.ScheduleEvent({0}, Region::kActive, act0);

  // Time 1: Preponed samples, Active sets value = 20.
  auto* prep1 = sched.GetEventPool().Acquire();
  prep1->callback = [&]() { preponed_samples.push_back(value); };
  sched.ScheduleEvent({1}, Region::kPreponed, prep1);

  auto* act1 = sched.GetEventPool().Acquire();
  act1->callback = [&]() { value = 20; };
  sched.ScheduleEvent({1}, Region::kActive, act1);

  // Time 2: Preponed samples.
  auto* prep2 = sched.GetEventPool().Acquire();
  prep2->callback = [&]() { preponed_samples.push_back(value); };
  sched.ScheduleEvent({2}, Region::kPreponed, prep2);

  sched.Run();
  ASSERT_EQ(preponed_samples.size(), 2u);
  EXPECT_EQ(preponed_samples[0], 10);
  EXPECT_EQ(preponed_samples[1], 20);
}
