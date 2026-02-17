#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.3.4 Post-NBA PLI region
//
// LRM §4.4.3.4:
//   "The Post-NBA region provides for a PLI callback control point that
//    allows PLI application routines to read and write values and create
//    events after the events in the NBA region are evaluated (see 4.5)."
//
// Figure 4-1 shows:
//   region_NBA -> pli_region_PostNBA -> region_PreObserved
//
// The Post-NBA region is a read-write PLI callback control point.
// Post-NBA is part of the active region set (§4.4.1).
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.3.4 "provides for a PLI callback control point"
// Basic: events scheduled in the Post-NBA region are executed.
// ---------------------------------------------------------------------------
TEST(SimCh4434, PostNBARegionExecutesPLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int executed = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { executed++; };
  sched.ScheduleEvent({0}, Region::kPostNBA, ev);

  sched.Run();
  EXPECT_EQ(executed, 1);
}

// ---------------------------------------------------------------------------
// §4.4.3.4 "allows PLI application routines to read ... values"
// A Post-NBA callback can read state set by the NBA region.
// ---------------------------------------------------------------------------
TEST(SimCh4434, PostNBACanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  // NBA sets value = 42.
  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { value = 42; };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  // Post-NBA reads value — should see 42.
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPostNBA, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

// ---------------------------------------------------------------------------
// §4.4.3.4 "allows PLI application routines to ... write values"
// A Post-NBA callback can modify state that later regions will observe.
// ---------------------------------------------------------------------------
TEST(SimCh4434, PostNBACanWriteValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled_in_observed = -1;

  // Post-NBA writes a value.
  auto* post_nba = sched.GetEventPool().Acquire();
  post_nba->callback = [&]() { value = 99; };
  sched.ScheduleEvent({0}, Region::kPostNBA, post_nba);

  // Observed reads the value — should see 99.
  auto* observed = sched.GetEventPool().Acquire();
  observed->callback = [&]() { sampled_in_observed = value; };
  sched.ScheduleEvent({0}, Region::kObserved, observed);

  sched.Run();
  EXPECT_EQ(sampled_in_observed, 99);
}

// ---------------------------------------------------------------------------
// §4.4.3.4 "allows PLI application routines to ... create events"
// A Post-NBA callback can schedule new events (e.g., into Observed).
// ---------------------------------------------------------------------------
TEST(SimCh4434, PostNBACanCreateEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* post_nba = sched.GetEventPool().Acquire();
  post_nba->callback = [&]() {
    order.push_back("post_nba");
    // Create an event in the Observed region from Post-NBA.
    auto* new_ev = sched.GetEventPool().Acquire();
    new_ev->callback = [&order]() { order.push_back("created_observed"); };
    sched.ScheduleEvent({0}, Region::kObserved, new_ev);
  };
  sched.ScheduleEvent({0}, Region::kPostNBA, post_nba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "post_nba");
  EXPECT_EQ(order[1], "created_observed");
}

// ---------------------------------------------------------------------------
// §4.4.3.4 "after the events in the NBA region are evaluated"
// Post-NBA executes after NBA in the same time slot.
// ---------------------------------------------------------------------------
TEST(SimCh4434, PostNBAExecutesAfterNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Schedule Post-NBA first, then NBA — ordering must still hold.
  auto* post_nba = sched.GetEventPool().Acquire();
  post_nba->callback = [&]() { order.push_back("post_nba"); };
  sched.ScheduleEvent({0}, Region::kPostNBA, post_nba);

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { order.push_back("nba"); };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "nba");
  EXPECT_EQ(order[1], "post_nba");
}

// ---------------------------------------------------------------------------
// §4.4.3.4 + Figure 4-1: NBA -> Post-NBA -> PreObserved.
// Post-NBA executes after NBA and before PreObserved.
// ---------------------------------------------------------------------------
TEST(SimCh4434, PostNBAExecutesAfterNBABeforePreObserved) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule in reverse order to prove region ordering.
  schedule(Region::kPreObserved, "pre_observed");
  schedule(Region::kPostNBA, "post_nba");
  schedule(Region::kNBA, "nba");

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "nba");
  EXPECT_EQ(order[1], "post_nba");
  EXPECT_EQ(order[2], "pre_observed");
}

// ---------------------------------------------------------------------------
// §4.4.3.4 Post-NBA is part of the active region set (§4.4.1).
// Its ordinal lies between NBA and PreObserved.
// ---------------------------------------------------------------------------
TEST(SimCh4434, PostNBAIsWithinActiveRegionSet) {
  auto post_nba_ord = static_cast<int>(Region::kPostNBA);
  auto nba_ord = static_cast<int>(Region::kNBA);
  auto pre_observed_ord = static_cast<int>(Region::kPreObserved);
  EXPECT_GT(post_nba_ord, nba_ord);
  EXPECT_LT(post_nba_ord, pre_observed_ord);
}

// ---------------------------------------------------------------------------
// §4.4.3.4 "PLI callback control point"
// Multiple PLI callbacks coexist in the Post-NBA region and all execute.
// ---------------------------------------------------------------------------
TEST(SimCh4434, PostNBARegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPostNBA, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

// ---------------------------------------------------------------------------
// §4.4.3.4 Post-NBA events across multiple time slots.
// Each time slot has its own Post-NBA region evaluation.
// ---------------------------------------------------------------------------
TEST(SimCh4434, PostNBAEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPostNBA, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

// ---------------------------------------------------------------------------
// §4.4.3.4 "read and write values and create events"
// Post-NBA is read-write. A Post-NBA callback reads state that NBA set
// earlier and overwrites it; a later Observed callback sees the Post-NBA
// modification. This verifies read-write capability in context.
// ---------------------------------------------------------------------------
TEST(SimCh4434, PostNBAReadWriteInActiveRegionSetContext) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int nba_sample = -1;
  int observed_sample = -1;

  // NBA writes value = 10.
  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { value = 10; };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  // Post-NBA reads the NBA-set value and overwrites it to 55.
  auto* post_nba = sched.GetEventPool().Acquire();
  post_nba->callback = [&]() {
    nba_sample = value;
    value = 55;
  };
  sched.ScheduleEvent({0}, Region::kPostNBA, post_nba);

  // Observed samples value — should see 55 from Post-NBA.
  auto* observed = sched.GetEventPool().Acquire();
  observed->callback = [&]() { observed_sample = value; };
  sched.ScheduleEvent({0}, Region::kObserved, observed);

  sched.Run();
  EXPECT_EQ(nba_sample, 10);
  EXPECT_EQ(observed_sample, 55);
}
