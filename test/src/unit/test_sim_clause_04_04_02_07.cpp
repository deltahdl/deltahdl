#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.2.7 Re-Inactive events region
//
// Figure 4-1 shows:
//   region_Reactive    -> region_ReInactive    (forward from Reactive)
//   region_ReInactive  -> region_Reactive      (feedback -- iteration)
//   region_ReInactive  -> pli_region_PreReNBA  (forward to PreReNBA PLI)
//
// The Re-Inactive region is part of the reactive region set (§4.4.1).
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.2.7 Re-Inactive region event execution
// Basic: events scheduled in the Re-Inactive region are executed.
// ---------------------------------------------------------------------------
TEST(SimCh4427, ReInactiveRegionExecutesEvents) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kReInactive, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

// ---------------------------------------------------------------------------
// §4.4.2.7 Re-Inactive executes after Reactive
// Re-Inactive events execute only after Reactive events have drained.
// ---------------------------------------------------------------------------
TEST(SimCh4427, ReInactiveExecutesAfterReactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* reinactive = sched.GetEventPool().Acquire();
  reinactive->callback = [&]() { order.push_back("reinactive"); };
  sched.ScheduleEvent({0}, Region::kReInactive, reinactive);

  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() { order.push_back("reactive"); };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "reactive");
  EXPECT_EQ(order[1], "reinactive");
}

// ---------------------------------------------------------------------------
// §4.4.2.7 All Reactive events complete before Re-Inactive
// Multiple Reactive events all complete before any Re-Inactive event starts.
// ---------------------------------------------------------------------------
TEST(SimCh4427, AllReactiveEventsCompleteBeforeReInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  for (int i = 0; i < 3; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() {
      order.push_back("reactive" + std::to_string(i));
    };
    sched.ScheduleEvent({0}, Region::kReactive, ev);
  }

  auto* reinactive = sched.GetEventPool().Acquire();
  reinactive->callback = [&]() { order.push_back("reinactive"); };
  sched.ScheduleEvent({0}, Region::kReInactive, reinactive);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  // All three reactive events come before reinactive.
  EXPECT_EQ(order[3], "reinactive");
}

// ---------------------------------------------------------------------------
// §4.4.2.7 #0 delay schedules into Re-Inactive
// Simulating #0: a Reactive callback schedules into Re-Inactive at the
// same time.
// ---------------------------------------------------------------------------
TEST(SimCh4427, ZeroDelaySchedulesIntoReInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() {
    order.push_back("reactive");
    // #0 delay: schedule into Re-Inactive at current time.
    auto* delayed = sched.GetEventPool().Acquire();
    delayed->callback = [&order]() { order.push_back("after_zero_delay"); };
    sched.ScheduleEvent({0}, Region::kReInactive, delayed);
  };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "reactive");
  EXPECT_EQ(order[1], "after_zero_delay");
}

// ---------------------------------------------------------------------------
// §4.4.2.7 Re-Inactive-to-Reactive iteration
// Figure 4-1: region_ReInactive -> region_Reactive (feedback edge).
// A Re-Inactive callback that schedules a new Reactive event triggers
// re-iteration of the reactive region set.
// ---------------------------------------------------------------------------
TEST(SimCh4427, ReInactiveToReactiveIteration) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Initial Reactive event schedules into Re-Inactive (#0).
  auto* react1 = sched.GetEventPool().Acquire();
  react1->callback = [&]() {
    order.push_back("reactive1");
    auto* reinact = sched.GetEventPool().Acquire();
    reinact->callback = [&]() {
      order.push_back("reinactive");
      // Re-Inactive schedules new Reactive event -> triggers re-iteration.
      auto* react2 = sched.GetEventPool().Acquire();
      react2->callback = [&order]() { order.push_back("reactive2"); };
      sched.ScheduleEvent({0}, Region::kReactive, react2);
    };
    sched.ScheduleEvent({0}, Region::kReInactive, reinact);
  };
  sched.ScheduleEvent({0}, Region::kReactive, react1);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "reactive1");
  EXPECT_EQ(order[1], "reinactive");
  EXPECT_EQ(order[2], "reactive2");
}

// ---------------------------------------------------------------------------
// §4.4.2.7 Multiple #0 delays: chained zero-delay scheduling.
// Reactive -> Re-Inactive -> Reactive -> Re-Inactive demonstrates
// repeated iteration (dual of Active -> Inactive chaining).
// ---------------------------------------------------------------------------
TEST(SimCh4427, ChainedZeroDelayIteration) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Inner chain: reactive2 -> reinactive2.
  auto log_reinactive2 = [&order]() { order.push_back("reinactive2"); };
  auto do_reactive2 = [&]() {
    order.push_back("reactive2");
    auto* reinact2 = sched.GetEventPool().Acquire();
    reinact2->callback = log_reinactive2;
    sched.ScheduleEvent({0}, Region::kReInactive, reinact2);
  };
  // Outer chain: reactive1 -> reinactive1 -> (inner chain).
  auto do_reinactive1 = [&]() {
    order.push_back("reinactive1");
    auto* react2 = sched.GetEventPool().Acquire();
    react2->callback = do_reactive2;
    sched.ScheduleEvent({0}, Region::kReactive, react2);
  };

  auto* react1 = sched.GetEventPool().Acquire();
  react1->callback = [&]() {
    order.push_back("reactive1");
    auto* reinact1 = sched.GetEventPool().Acquire();
    reinact1->callback = do_reinactive1;
    sched.ScheduleEvent({0}, Region::kReInactive, reinact1);
  };
  sched.ScheduleEvent({0}, Region::kReactive, react1);

  sched.Run();
  std::vector<std::string> expected = {"reactive1", "reinactive1", "reactive2",
                                       "reinactive2"};
  EXPECT_EQ(order, expected);
}

// ---------------------------------------------------------------------------
// §4.4.2.7 Re-Inactive is part of the reactive region set (§4.4.1).
// Its ordinal lies between Reactive and PrePostponed.
// ---------------------------------------------------------------------------
TEST(SimCh4427, ReInactiveIsWithinReactiveRegionSet) {
  auto reinactive_ord = static_cast<int>(Region::kReInactive);
  auto reactive_ord = static_cast<int>(Region::kReactive);
  auto pre_postponed_ord = static_cast<int>(Region::kPrePostponed);
  EXPECT_GT(reinactive_ord, reactive_ord);
  EXPECT_LT(reinactive_ord, pre_postponed_ord);
}

// ---------------------------------------------------------------------------
// §4.4.2.7 Figure 4-1: region_ReInactive -> pli_region_PreReNBA.
// After Re-Inactive drains and no feedback to Reactive, the flow proceeds
// to PreReNBA/ReNBA.  This test verifies Re-Inactive executes before ReNBA.
// ---------------------------------------------------------------------------
TEST(SimCh4427, ReInactiveExecutesBeforeReNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* renba = sched.GetEventPool().Acquire();
  renba->callback = [&]() { order.push_back("renba"); };
  sched.ScheduleEvent({0}, Region::kReNBA, renba);

  auto* reinactive = sched.GetEventPool().Acquire();
  reinactive->callback = [&]() { order.push_back("reinactive"); };
  sched.ScheduleEvent({0}, Region::kReInactive, reinactive);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "reinactive");
  EXPECT_EQ(order[1], "renba");
}

// ---------------------------------------------------------------------------
// §4.4.2.7 Re-Inactive events across multiple time slots.
// Each time slot has its own Re-Inactive region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh4427, ReInactiveEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kReInactive, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

// ---------------------------------------------------------------------------
// §4.4.2.7 Multiple Re-Inactive events coexist and all execute.
// ---------------------------------------------------------------------------
TEST(SimCh4427, ReInactiveRegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kReInactive, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}
