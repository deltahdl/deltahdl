#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.2.5 Observed events region
//
// LRM §4.4.2.5:
//   "The Observed region is for evaluation of property expressions when
//    they are triggered."
//
//   "During property evaluation, pass/fail code shall be scheduled in
//    the Reactive region of the current time slot."
//
//   "PLI callbacks are not allowed in the Observed region."
//
// Figure 4-1 shows:
//   pli_region_PreObserved -> region_Observed  (forward from PreObserved PLI)
//   region_Observed -> pli_region_PostObserved (forward to PostObserved PLI)
//   region_Observed -> region_Active           (feedback — re-iteration)
//
// The Observed region is the first region of the reactive region set
// (§4.4.1) and bridges the active and reactive region sets.
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.2.5 "The Observed region is for evaluation of property expressions
// when they are triggered."
// Basic: events scheduled in the Observed region are executed.
// ---------------------------------------------------------------------------
TEST(SimCh4425, ObservedRegionExecutesEvents) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kObserved, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

// ---------------------------------------------------------------------------
// §4.4.2.5 "The Observed region is for evaluation of property expressions"
// Multiple property evaluation events coexist and all execute.
// ---------------------------------------------------------------------------
TEST(SimCh4425, ObservedRegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kObserved, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

// ---------------------------------------------------------------------------
// §4.4.2.5 "During property evaluation, pass/fail code shall be scheduled
// in the Reactive region of the current time slot."
// An Observed callback schedules into Reactive at the same time slot.
// ---------------------------------------------------------------------------
TEST(SimCh4425, ObservedSchedulesPassFailIntoReactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* obs = sched.GetEventPool().Acquire();
  obs->callback = [&]() {
    order.push_back("observed");
    // Property pass/fail action: schedule into Reactive.
    auto* reactive = sched.GetEventPool().Acquire();
    reactive->callback = [&order]() { order.push_back("reactive"); };
    sched.ScheduleEvent({0}, Region::kReactive, reactive);
  };
  sched.ScheduleEvent({0}, Region::kObserved, obs);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "observed");
  EXPECT_EQ(order[1], "reactive");
}

// ---------------------------------------------------------------------------
// §4.4.2.5 "pass/fail code shall be scheduled in the Reactive region of
// the current time slot"
// Multiple pass/fail actions from a single Observed event all land in
// Reactive at the current time slot.
// ---------------------------------------------------------------------------
TEST(SimCh4425, MultiplePassFailActionsScheduledInReactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* obs = sched.GetEventPool().Acquire();
  obs->callback = [&]() {
    order.push_back("observed");
    for (int i = 0; i < 3; ++i) {
      auto* r = sched.GetEventPool().Acquire();
      r->callback = [&order, i]() {
        order.push_back("reactive" + std::to_string(i));
      };
      sched.ScheduleEvent({0}, Region::kReactive, r);
    }
  };
  sched.ScheduleEvent({0}, Region::kObserved, obs);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "observed");
  // All three reactive events execute after observed.
  EXPECT_EQ(order[1], "reactive0");
  EXPECT_EQ(order[2], "reactive1");
  EXPECT_EQ(order[3], "reactive2");
}

// ---------------------------------------------------------------------------
// §4.4.2.5 Observed executes after NBA (and the entire active region set).
// This confirms its position in the region ordering per §4.4.2.
// ---------------------------------------------------------------------------
TEST(SimCh4425, ObservedExecutesAfterActiveRegionSet) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule in reverse order to prove region ordering, not insertion order.
  schedule(Region::kObserved, "observed");
  schedule(Region::kNBA, "nba");
  schedule(Region::kInactive, "inactive");
  schedule(Region::kActive, "active");

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "inactive");
  EXPECT_EQ(order[2], "nba");
  EXPECT_EQ(order[3], "observed");
}

// ---------------------------------------------------------------------------
// §4.4.2.5 + Figure 4-1: region_Observed -> region_Active (feedback edge).
// An Observed callback that schedules a new Active event triggers
// re-iteration of the active region set before continuing with Reactive.
// ---------------------------------------------------------------------------
TEST(SimCh4425, ObservedToActiveRestart) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* obs = sched.GetEventPool().Acquire();
  obs->callback = [&]() {
    order.push_back("observed");
    // Observed schedules a new Active event -> restarts active set.
    auto* act = sched.GetEventPool().Acquire();
    act->callback = [&order]() { order.push_back("active_restart"); };
    sched.ScheduleEvent({0}, Region::kActive, act);
  };
  sched.ScheduleEvent({0}, Region::kObserved, obs);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "observed");
  EXPECT_EQ(order[1], "active_restart");
}

// ---------------------------------------------------------------------------
// §4.4.2.5 Observed region ordinal lies between PostNBA and PostObserved.
// This verifies the enum ordering matches the LRM region sequence.
// ---------------------------------------------------------------------------
TEST(SimCh4425, ObservedIsAfterPostNBABeforePostObserved) {
  auto observed_ord = static_cast<int>(Region::kObserved);
  auto post_nba_ord = static_cast<int>(Region::kPostNBA);
  auto post_observed_ord = static_cast<int>(Region::kPostObserved);
  EXPECT_GT(observed_ord, post_nba_ord);
  EXPECT_LT(observed_ord, post_observed_ord);
}

// ---------------------------------------------------------------------------
// §4.4.2.5 + Figure 4-1: pli_region_PreObserved -> region_Observed.
// PreObserved PLI region executes before Observed.
// ---------------------------------------------------------------------------
TEST(SimCh4425, PreObservedExecutesBeforeObserved) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* obs = sched.GetEventPool().Acquire();
  obs->callback = [&]() { order.push_back("observed"); };
  sched.ScheduleEvent({0}, Region::kObserved, obs);

  auto* pre_obs = sched.GetEventPool().Acquire();
  pre_obs->callback = [&]() { order.push_back("pre_observed"); };
  sched.ScheduleEvent({0}, Region::kPreObserved, pre_obs);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_observed");
  EXPECT_EQ(order[1], "observed");
}

// ---------------------------------------------------------------------------
// §4.4.2.5 + Figure 4-1: region_Observed -> pli_region_PostObserved.
// Observed region executes before PostObserved PLI region.
// ---------------------------------------------------------------------------
TEST(SimCh4425, ObservedExecutesBeforePostObserved) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* post_obs = sched.GetEventPool().Acquire();
  post_obs->callback = [&]() { order.push_back("post_observed"); };
  sched.ScheduleEvent({0}, Region::kPostObserved, post_obs);

  auto* obs = sched.GetEventPool().Acquire();
  obs->callback = [&]() { order.push_back("observed"); };
  sched.ScheduleEvent({0}, Region::kObserved, obs);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "observed");
  EXPECT_EQ(order[1], "post_observed");
}

// ---------------------------------------------------------------------------
// §4.4.2.5 Observed events across multiple time slots.
// Each time slot has its own Observed region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh4425, ObservedEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kObserved, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}
