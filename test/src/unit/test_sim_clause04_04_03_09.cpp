#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.3.9 Pre-Postponed PLI region
//
// LRM §4.4.3.9:
//   "The Pre-Postponed region provides a PLI callback control point that
//    allows PLI application routines to read and write values and create
//    events after processing all other regions except the Postponed region."
//
// Figure 4-1 shows:
//   pli_region_PostReNBA -> pli_region_PrePostponed -> region_Postponed
//
// The Pre-Postponed region is a read-write PLI callback control point.
// Pre-Postponed is part of the reactive region set (§4.4.1 iterative regions).
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.3.9 "provides a PLI callback control point"
// Basic: events scheduled in the Pre-Postponed region are executed.
// ---------------------------------------------------------------------------
TEST(SimCh4439, PrePostponedRegionExecutesPLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kPrePostponed, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

// ---------------------------------------------------------------------------
// §4.4.3.9 "allows PLI application routines to read ... values"
// A Pre-Postponed callback can read state set by an earlier region.
// ---------------------------------------------------------------------------
TEST(SimCh4439, PrePostponedCanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  // Post-Re-NBA sets value = 42.
  auto* post_re_nba = sched.GetEventPool().Acquire();
  post_re_nba->callback = [&]() { value = 42; };
  sched.ScheduleEvent({0}, Region::kPostReNBA, post_re_nba);

  // Pre-Postponed reads value — should see 42.
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPrePostponed, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

// ---------------------------------------------------------------------------
// §4.4.3.9 "allows PLI application routines to ... write values"
// A Pre-Postponed callback can modify state that Postponed will observe.
// ---------------------------------------------------------------------------
TEST(SimCh4439, PrePostponedCanWriteValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled_in_postponed = -1;

  // Pre-Postponed writes a value.
  auto* pre_postponed = sched.GetEventPool().Acquire();
  pre_postponed->callback = [&]() { value = 99; };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pre_postponed);

  // Postponed reads the value — should see 99.
  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { sampled_in_postponed = value; };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  EXPECT_EQ(sampled_in_postponed, 99);
}

// ---------------------------------------------------------------------------
// §4.4.3.9 "allows PLI application routines to ... create events"
// A Pre-Postponed callback can schedule new events (e.g., into Postponed).
// ---------------------------------------------------------------------------
TEST(SimCh4439, PrePostponedCanCreateEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* pre_postponed = sched.GetEventPool().Acquire();
  pre_postponed->callback = [&]() {
    order.push_back("pre_postponed");
    // Create an event in the Postponed region from Pre-Postponed.
    auto* new_ev = sched.GetEventPool().Acquire();
    new_ev->callback = [&order]() { order.push_back("created_postponed"); };
    sched.ScheduleEvent({0}, Region::kPostponed, new_ev);
  };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pre_postponed);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_postponed");
  EXPECT_EQ(order[1], "created_postponed");
}

// ---------------------------------------------------------------------------
// §4.4.3.9 "after processing all other regions except the Postponed region"
// Pre-Postponed executes after Post-Re-NBA in the same time slot.
// ---------------------------------------------------------------------------
TEST(SimCh4439, PrePostponedExecutesAfterPostReNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Schedule Pre-Postponed first, then Post-Re-NBA — ordering must hold.
  auto* pre_postponed = sched.GetEventPool().Acquire();
  pre_postponed->callback = [&]() { order.push_back("pre_postponed"); };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pre_postponed);

  auto* post_re_nba = sched.GetEventPool().Acquire();
  post_re_nba->callback = [&]() { order.push_back("post_re_nba"); };
  sched.ScheduleEvent({0}, Region::kPostReNBA, post_re_nba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "post_re_nba");
  EXPECT_EQ(order[1], "pre_postponed");
}

// ---------------------------------------------------------------------------
// §4.4.3.9 + Figure 4-1: PostReNBA -> PrePostponed -> Postponed.
// Pre-Postponed executes after Post-Re-NBA and before Postponed.
// ---------------------------------------------------------------------------
TEST(SimCh4439, PrePostponedExecutesAfterPostReNBABeforePostponed) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule in reverse order to prove region ordering.
  schedule(Region::kPostponed, "postponed");
  schedule(Region::kPrePostponed, "pre_postponed");
  schedule(Region::kPostReNBA, "post_re_nba");

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "post_re_nba");
  EXPECT_EQ(order[1], "pre_postponed");
  EXPECT_EQ(order[2], "postponed");
}

// ---------------------------------------------------------------------------
// §4.4.3.9 Pre-Postponed is part of the reactive region set (§4.4.1).
// Its ordinal lies between Post-Re-NBA and Postponed.
// ---------------------------------------------------------------------------
TEST(SimCh4439, PrePostponedIsWithinReactiveRegionSet) {
  auto pre_postponed_ord = static_cast<int>(Region::kPrePostponed);
  auto post_re_nba_ord = static_cast<int>(Region::kPostReNBA);
  auto postponed_ord = static_cast<int>(Region::kPostponed);
  EXPECT_GT(pre_postponed_ord, post_re_nba_ord);
  EXPECT_LT(pre_postponed_ord, postponed_ord);
}

// ---------------------------------------------------------------------------
// §4.4.3.9 "PLI callback control point"
// Multiple PLI callbacks coexist in the Pre-Postponed region and all execute.
// ---------------------------------------------------------------------------
TEST(SimCh4439, PrePostponedRegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPrePostponed, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

// ---------------------------------------------------------------------------
// §4.4.3.9 Pre-Postponed events across multiple time slots.
// Each time slot has its own Pre-Postponed region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh4439, PrePostponedEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPrePostponed, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

// ---------------------------------------------------------------------------
// §4.4.3.9 "read and write values and create events"
// Pre-Postponed is read-write. A Pre-Postponed callback reads state that
// Post-Re-NBA set earlier and overwrites it; a later Postponed callback sees
// the Pre-Postponed modification. This verifies read-write capability.
// ---------------------------------------------------------------------------
TEST(SimCh4439, PrePostponedReadWriteInReactiveRegionSetContext) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int post_re_nba_sample = -1;
  int postponed_sample = -1;

  // Post-Re-NBA writes value = 10.
  auto* post_re_nba = sched.GetEventPool().Acquire();
  post_re_nba->callback = [&]() { value = 10; };
  sched.ScheduleEvent({0}, Region::kPostReNBA, post_re_nba);

  // Pre-Postponed reads the Post-Re-NBA-set value and overwrites it to 55.
  auto* pre_postponed = sched.GetEventPool().Acquire();
  pre_postponed->callback = [&]() {
    post_re_nba_sample = value;
    value = 55;
  };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pre_postponed);

  // Postponed samples value — should see 55 from Pre-Postponed.
  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { postponed_sample = value; };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  EXPECT_EQ(post_re_nba_sample, 10);
  EXPECT_EQ(postponed_sample, 55);
}
