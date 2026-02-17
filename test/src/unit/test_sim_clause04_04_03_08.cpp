#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.3.8 Post-Re-NBA PLI region
//
// LRM §4.4.3.8:
//   "The Post-Re-NBA region provides for a PLI callback control point that
//    allows PLI application routines to read and write values and create
//    events after the events in the Re-NBA region are evaluated (see 4.5)."
//
// Figure 4-1 shows:
//   region_ReNBA -> pli_region_PostReNBA -> pli_region_PrePostponed
//
// The Post-Re-NBA region is a read-write PLI callback control point.
// Post-Re-NBA is part of the reactive region set (§4.4.1 iterative regions).
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.3.8 "provides for a PLI callback control point"
// Basic: events scheduled in the Post-Re-NBA region are executed.
// ---------------------------------------------------------------------------
TEST(SimCh4438, PostReNBARegionExecutesPLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kPostReNBA, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

// ---------------------------------------------------------------------------
// §4.4.3.8 "allows PLI application routines to read ... values"
// A Post-Re-NBA callback can read state set by an earlier region.
// ---------------------------------------------------------------------------
TEST(SimCh4438, PostReNBACanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  // Re-NBA sets value = 42.
  auto* re_nba = sched.GetEventPool().Acquire();
  re_nba->callback = [&]() { value = 42; };
  sched.ScheduleEvent({0}, Region::kReNBA, re_nba);

  // Post-Re-NBA reads value — should see 42.
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPostReNBA, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

// ---------------------------------------------------------------------------
// §4.4.3.8 "allows PLI application routines to ... write values"
// A Post-Re-NBA callback can modify state that later regions will observe.
// ---------------------------------------------------------------------------
TEST(SimCh4438, PostReNBACanWriteValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled_in_pre_postponed = -1;

  // Post-Re-NBA writes a value.
  auto* post_re_nba = sched.GetEventPool().Acquire();
  post_re_nba->callback = [&]() { value = 99; };
  sched.ScheduleEvent({0}, Region::kPostReNBA, post_re_nba);

  // Pre-Postponed reads the value — should see 99.
  auto* pre_postponed = sched.GetEventPool().Acquire();
  pre_postponed->callback = [&]() { sampled_in_pre_postponed = value; };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pre_postponed);

  sched.Run();
  EXPECT_EQ(sampled_in_pre_postponed, 99);
}

// ---------------------------------------------------------------------------
// §4.4.3.8 "allows PLI application routines to ... create events"
// A Post-Re-NBA callback can schedule new events (e.g., into Pre-Postponed).
// ---------------------------------------------------------------------------
TEST(SimCh4438, PostReNBACanCreateEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* post_re_nba = sched.GetEventPool().Acquire();
  post_re_nba->callback = [&]() {
    order.push_back("post_re_nba");
    // Create an event in the Pre-Postponed region from Post-Re-NBA.
    auto* new_ev = sched.GetEventPool().Acquire();
    new_ev->callback = [&order]() {
      order.push_back("created_pre_postponed");
    };
    sched.ScheduleEvent({0}, Region::kPrePostponed, new_ev);
  };
  sched.ScheduleEvent({0}, Region::kPostReNBA, post_re_nba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "post_re_nba");
  EXPECT_EQ(order[1], "created_pre_postponed");
}

// ---------------------------------------------------------------------------
// §4.4.3.8 "after the events in the Re-NBA region are evaluated"
// Post-Re-NBA executes after Re-NBA in the same time slot.
// ---------------------------------------------------------------------------
TEST(SimCh4438, PostReNBAExecutesAfterReNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Schedule Post-Re-NBA first, then Re-NBA — ordering must still hold.
  auto* post_re_nba = sched.GetEventPool().Acquire();
  post_re_nba->callback = [&]() { order.push_back("post_re_nba"); };
  sched.ScheduleEvent({0}, Region::kPostReNBA, post_re_nba);

  auto* re_nba = sched.GetEventPool().Acquire();
  re_nba->callback = [&]() { order.push_back("re_nba"); };
  sched.ScheduleEvent({0}, Region::kReNBA, re_nba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "re_nba");
  EXPECT_EQ(order[1], "post_re_nba");
}

// ---------------------------------------------------------------------------
// §4.4.3.8 + Figure 4-1: ReNBA -> PostReNBA -> PrePostponed.
// Post-Re-NBA executes after Re-NBA and before Pre-Postponed.
// ---------------------------------------------------------------------------
TEST(SimCh4438, PostReNBAExecutesAfterReNBABeforePrePostponed) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule in reverse order to prove region ordering.
  schedule(Region::kPrePostponed, "pre_postponed");
  schedule(Region::kPostReNBA, "post_re_nba");
  schedule(Region::kReNBA, "re_nba");

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "re_nba");
  EXPECT_EQ(order[1], "post_re_nba");
  EXPECT_EQ(order[2], "pre_postponed");
}

// ---------------------------------------------------------------------------
// §4.4.3.8 Post-Re-NBA is part of the reactive region set (§4.4.1).
// Its ordinal lies between Re-NBA and Pre-Postponed.
// ---------------------------------------------------------------------------
TEST(SimCh4438, PostReNBAIsWithinReactiveRegionSet) {
  auto post_re_nba_ord = static_cast<int>(Region::kPostReNBA);
  auto re_nba_ord = static_cast<int>(Region::kReNBA);
  auto pre_postponed_ord = static_cast<int>(Region::kPrePostponed);
  EXPECT_GT(post_re_nba_ord, re_nba_ord);
  EXPECT_LT(post_re_nba_ord, pre_postponed_ord);
}

// ---------------------------------------------------------------------------
// §4.4.3.8 "PLI callback control point"
// Multiple PLI callbacks coexist in the Post-Re-NBA region and all execute.
// ---------------------------------------------------------------------------
TEST(SimCh4438, PostReNBARegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPostReNBA, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

// ---------------------------------------------------------------------------
// §4.4.3.8 Post-Re-NBA events across multiple time slots.
// Each time slot has its own Post-Re-NBA region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh4438, PostReNBAEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPostReNBA, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

// ---------------------------------------------------------------------------
// §4.4.3.8 "read and write values and create events"
// Post-Re-NBA is read-write. A Post-Re-NBA callback reads state that Re-NBA
// set earlier and overwrites it; a later Pre-Postponed callback sees the
// Post-Re-NBA modification. This verifies read-write capability in context.
// ---------------------------------------------------------------------------
TEST(SimCh4438, PostReNBAReadWriteInReactiveRegionSetContext) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int re_nba_sample = -1;
  int pre_postponed_sample = -1;

  // Re-NBA writes value = 10.
  auto* re_nba = sched.GetEventPool().Acquire();
  re_nba->callback = [&]() { value = 10; };
  sched.ScheduleEvent({0}, Region::kReNBA, re_nba);

  // Post-Re-NBA reads the Re-NBA-set value and overwrites it to 55.
  auto* post_re_nba = sched.GetEventPool().Acquire();
  post_re_nba->callback = [&]() {
    re_nba_sample = value;
    value = 55;
  };
  sched.ScheduleEvent({0}, Region::kPostReNBA, post_re_nba);

  // Pre-Postponed samples value — should see 55 from Post-Re-NBA.
  auto* pre_postponed = sched.GetEventPool().Acquire();
  pre_postponed->callback = [&]() { pre_postponed_sample = value; };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pre_postponed);

  sched.Run();
  EXPECT_EQ(re_nba_sample, 10);
  EXPECT_EQ(pre_postponed_sample, 55);
}
