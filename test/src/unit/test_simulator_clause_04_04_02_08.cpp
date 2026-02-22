#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.2.8 Re-NBA events region
//
// Figure 4-1 shows:
//   pli_region_PreReNBA -> region_ReNBA    (forward from PreReNBA PLI)
//   region_ReNBA -> pli_region_PostReNBA   (forward to PostReNBA PLI)
//   region_ReNBA -> region_Reactive        (feedback -- re-iteration)
//
// The Re-NBA region is part of the reactive region set (§4.4.1).
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.2.8 Re-NBA region event execution
// Basic: events scheduled in the Re-NBA region are executed.
// ---------------------------------------------------------------------------
TEST(SimCh4428, ReNBARegionExecutesEvents) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto *ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kReNBA, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

// ---------------------------------------------------------------------------
// §4.4.2.8 Re-NBA executes after Re-Inactive
// Re-NBA events execute only after Re-Inactive events have drained.
// ---------------------------------------------------------------------------
TEST(SimCh4428, ReNBAExecutesAfterReInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto *renba = sched.GetEventPool().Acquire();
  renba->callback = [&]() { order.push_back("renba"); };
  sched.ScheduleEvent({0}, Region::kReNBA, renba);

  auto *reinactive = sched.GetEventPool().Acquire();
  reinactive->callback = [&]() { order.push_back("reinactive"); };
  sched.ScheduleEvent({0}, Region::kReInactive, reinactive);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "reinactive");
  EXPECT_EQ(order[1], "renba");
}

// ---------------------------------------------------------------------------
// §4.4.2.8 All Re-Inactive events complete before Re-NBA
// Multiple Re-Inactive events all complete before any Re-NBA event starts.
// ---------------------------------------------------------------------------
TEST(SimCh4428, AllReInactiveEventsCompleteBeforeReNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  for (int i = 0; i < 3; ++i) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() {
      order.push_back("reinactive" + std::to_string(i));
    };
    sched.ScheduleEvent({0}, Region::kReInactive, ev);
  }

  auto *renba = sched.GetEventPool().Acquire();
  renba->callback = [&]() { order.push_back("renba"); };
  sched.ScheduleEvent({0}, Region::kReNBA, renba);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  // All three Re-Inactive events come before Re-NBA.
  EXPECT_EQ(order[3], "renba");
}

// ---------------------------------------------------------------------------
// §4.4.2.8 Nonblocking assignment schedules Re-NBA at current time
// A Reactive callback schedules into Re-NBA at the same time (current time).
// ---------------------------------------------------------------------------
TEST(SimCh4428, NonblockingAssignmentSchedulesReNBACurrentTime) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto *reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() {
    order.push_back("reactive");
    // Nonblocking assignment: schedule Re-NBA at current time.
    auto *renba = sched.GetEventPool().Acquire();
    renba->callback = [&order]() { order.push_back("renba"); };
    sched.ScheduleEvent({0}, Region::kReNBA, renba);
  };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "reactive");
  EXPECT_EQ(order[1], "renba");
}

// ---------------------------------------------------------------------------
// §4.4.2.8 Nonblocking assignment schedules Re-NBA at later time
// A Reactive callback at time 0 schedules a Re-NBA event at time 5.
// ---------------------------------------------------------------------------
TEST(SimCh4428, NonblockingAssignmentSchedulesReNBALaterTime) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> renba_times;

  auto *reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() {
    // Nonblocking assignment with delay: schedule Re-NBA at a later time.
    auto *renba = sched.GetEventPool().Acquire();
    renba->callback = [&renba_times, &sched]() {
      renba_times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({5}, Region::kReNBA, renba);
  };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  sched.Run();
  ASSERT_EQ(renba_times.size(), 1u);
  EXPECT_EQ(renba_times[0], 5u);
}

// ---------------------------------------------------------------------------
// §4.4.2.8 + Figure 4-1: region_ReNBA -> region_Reactive (feedback edge).
// A Re-NBA callback that schedules a new Reactive event triggers
// re-iteration of the reactive region set.
// ---------------------------------------------------------------------------
TEST(SimCh4428, ReNBAToReactiveIteration) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Initial Reactive event schedules a Re-NBA.
  auto *react1 = sched.GetEventPool().Acquire();
  react1->callback = [&]() {
    order.push_back("reactive1");
    auto *renba = sched.GetEventPool().Acquire();
    renba->callback = [&]() {
      order.push_back("renba");
      // Re-NBA schedules a new Reactive event -> triggers re-iteration.
      auto *react2 = sched.GetEventPool().Acquire();
      react2->callback = [&order]() { order.push_back("reactive2"); };
      sched.ScheduleEvent({0}, Region::kReactive, react2);
    };
    sched.ScheduleEvent({0}, Region::kReNBA, renba);
  };
  sched.ScheduleEvent({0}, Region::kReactive, react1);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "reactive1");
  EXPECT_EQ(order[1], "renba");
  EXPECT_EQ(order[2], "reactive2");
}

// ---------------------------------------------------------------------------
// §4.4.2.8 Re-NBA executes after Reactive and Re-Inactive, before
// PostReNBA.  This confirms its position in the region ordering per §4.4.2.
// ---------------------------------------------------------------------------
TEST(SimCh4428, ReNBAExecutesAfterReactiveAndReInactiveBeforePostReNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string &label) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule in reverse order to prove region ordering, not insertion order.
  schedule(Region::kPostReNBA, "post_renba");
  schedule(Region::kReNBA, "renba");
  schedule(Region::kReInactive, "reinactive");
  schedule(Region::kReactive, "reactive");

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "reactive");
  EXPECT_EQ(order[1], "reinactive");
  EXPECT_EQ(order[2], "renba");
  EXPECT_EQ(order[3], "post_renba");
}

// ---------------------------------------------------------------------------
// §4.4.2.8 Re-NBA is part of the reactive region set (§4.4.1).
// Its ordinal lies between ReInactive and PostReNBA.
// ---------------------------------------------------------------------------
TEST(SimCh4428, ReNBAIsWithinReactiveRegionSet) {
  auto renba_ord = static_cast<int>(Region::kReNBA);
  auto reinactive_ord = static_cast<int>(Region::kReInactive);
  auto post_renba_ord = static_cast<int>(Region::kPostReNBA);
  EXPECT_GT(renba_ord, reinactive_ord);
  EXPECT_LT(renba_ord, post_renba_ord);
}

// ---------------------------------------------------------------------------
// §4.4.2.8 Re-NBA events across multiple time slots.
// Each time slot has its own Re-NBA region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh4428, ReNBAEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kReNBA, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

// ---------------------------------------------------------------------------
// §4.4.2.8 Multiple Re-NBA events coexist and all execute.
// ---------------------------------------------------------------------------
TEST(SimCh4428, ReNBARegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kReNBA, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}
