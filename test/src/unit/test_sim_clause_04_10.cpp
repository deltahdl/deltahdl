#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.10 PLI callback control points
//
// LRM §4.10:
//   "There are two kinds of PLI callbacks: those that are executed immediately
//    when some specific activity occurs, and those that are explicitly
//    registered as a one-shot evaluation event."
//
//   Table 4-1 provides the mapping from the various PLI callbacks:
//     cbAfterDelay       → Pre-Active
//     cbNextSimTime      → Pre-Active
//     cbReadWriteSynch   → Pre-NBA or Post-NBA
//     cbAtStartOfSimTime → Pre-Active
//     cbNBASynch         → Pre-NBA
//     cbAtEndOfSimTime   → Pre-Postponed
//     cbReadOnlySynch    → Postponed
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.10 "There are two kinds of PLI callbacks: those that are executed
//         immediately when some specific activity occurs"
// Immediate-execution callbacks fire synchronously when their triggering
// activity happens, without being scheduled through the event regions.
// ---------------------------------------------------------------------------
TEST(SimCh410, ImmediateExecutionCallback) {
  Arena arena;
  Scheduler sched(arena);
  bool callback_fired = false;
  bool activity_occurred = false;

  // Model: A PLI callback that fires immediately when an activity occurs.
  // The callback executes synchronously within the triggering event.
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    activity_occurred = true;
    // Immediate PLI callback — fires synchronously during the activity.
    callback_fired = true;
    // Both flags are true at this point — no scheduling delay.
    EXPECT_TRUE(activity_occurred);
    EXPECT_TRUE(callback_fired);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_TRUE(activity_occurred);
  EXPECT_TRUE(callback_fired);
}

// ---------------------------------------------------------------------------
// §4.10 "and those that are explicitly registered as a one-shot evaluation
//         event"
// One-shot callbacks are registered in a specific event region and execute
// exactly once when the scheduler processes that region.
// ---------------------------------------------------------------------------
TEST(SimCh410, OneShotEvaluationEvent) {
  Arena arena;
  Scheduler sched(arena);
  int fire_count = 0;

  // Model: A one-shot PLI callback registered in Pre-Active.
  // It executes exactly once when the Pre-Active region is processed.
  auto* oneshot = sched.GetEventPool().Acquire();
  oneshot->kind = EventKind::kEvaluation;
  oneshot->callback = [&]() { fire_count++; };
  sched.ScheduleEvent({0}, Region::kPreActive, oneshot);

  sched.Run();
  // One-shot: fires exactly once.
  EXPECT_EQ(fire_count, 1);
}

// ---------------------------------------------------------------------------
// Table 4-1: cbAfterDelay → Pre-Active
// A cbAfterDelay callback is scheduled in the Pre-Active region. It executes
// before Active-region events at the target time step.
// ---------------------------------------------------------------------------
TEST(SimCh410, CbAfterDelayInPreActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Model: cbAfterDelay registered at time 5 → Pre-Active.
  auto* cb = sched.GetEventPool().Acquire();
  cb->kind = EventKind::kEvaluation;
  cb->callback = [&]() { order.push_back("pre_active_cb"); };
  sched.ScheduleEvent({5}, Region::kPreActive, cb);

  // An Active event at the same time.
  auto* active = sched.GetEventPool().Acquire();
  active->kind = EventKind::kEvaluation;
  active->callback = [&]() { order.push_back("active_event"); };
  sched.ScheduleEvent({5}, Region::kActive, active);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_active_cb");
  EXPECT_EQ(order[1], "active_event");
}

// ---------------------------------------------------------------------------
// Table 4-1: cbNextSimTime → Pre-Active
// A cbNextSimTime callback is also scheduled in the Pre-Active region.
// It fires before Active events when the next simulation time step begins.
// ---------------------------------------------------------------------------
TEST(SimCh410, CbNextSimTimeInPreActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Model: cbNextSimTime fires at time 10 (next sim time) → Pre-Active.
  auto* cb = sched.GetEventPool().Acquire();
  cb->kind = EventKind::kEvaluation;
  cb->callback = [&]() { order.push_back("pre_active_nextsim"); };
  sched.ScheduleEvent({10}, Region::kPreActive, cb);

  auto* active = sched.GetEventPool().Acquire();
  active->kind = EventKind::kEvaluation;
  active->callback = [&]() { order.push_back("active_event"); };
  sched.ScheduleEvent({10}, Region::kActive, active);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_active_nextsim");
  EXPECT_EQ(order[1], "active_event");
}

// ---------------------------------------------------------------------------
// Table 4-1: cbAtStartOfSimTime → Pre-Active
// A cbAtStartOfSimTime callback fires in the Pre-Active region, before any
// Active events at the beginning of the time step.
// ---------------------------------------------------------------------------
TEST(SimCh410, CbAtStartOfSimTimeInPreActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Model: cbAtStartOfSimTime → Pre-Active at time 0.
  auto* cb = sched.GetEventPool().Acquire();
  cb->kind = EventKind::kEvaluation;
  cb->callback = [&]() { order.push_back("pre_active_start"); };
  sched.ScheduleEvent({0}, Region::kPreActive, cb);

  auto* active = sched.GetEventPool().Acquire();
  active->kind = EventKind::kEvaluation;
  active->callback = [&]() { order.push_back("active_event"); };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_active_start");
  EXPECT_EQ(order[1], "active_event");
}

// ---------------------------------------------------------------------------
// Table 4-1: cbNBASynch → Pre-NBA
// A cbNBASynch callback fires in the Pre-NBA region, after Active/Inactive
// events and before NBA events.
// ---------------------------------------------------------------------------
TEST(SimCh410, CbNbaSynchInPreNba) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Schedule Active, Pre-NBA, and NBA events to verify ordering.
  auto* active = sched.GetEventPool().Acquire();
  active->kind = EventKind::kEvaluation;
  active->callback = [&]() {
    order.push_back("active");
    // Schedule NBA from Active region.
    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&]() { order.push_back("nba"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  // cbNBASynch → Pre-NBA.
  auto* cb = sched.GetEventPool().Acquire();
  cb->kind = EventKind::kEvaluation;
  cb->callback = [&]() { order.push_back("pre_nba_cb"); };
  sched.ScheduleEvent({0}, Region::kPreNBA, cb);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "pre_nba_cb");
  EXPECT_EQ(order[2], "nba");
}

// ---------------------------------------------------------------------------
// Table 4-1: cbReadWriteSynch → Pre-NBA or Post-NBA
// A cbReadWriteSynch callback fires in either Pre-NBA or Post-NBA. This test
// verifies both placements execute at the correct points relative to NBA.
// ---------------------------------------------------------------------------
TEST(SimCh410, CbReadWriteSynchInPreNbaOrPostNba) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Active event that schedules an NBA.
  auto* active = sched.GetEventPool().Acquire();
  active->kind = EventKind::kEvaluation;
  active->callback = [&]() {
    order.push_back("active");
    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&]() { order.push_back("nba"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  // cbReadWriteSynch in Pre-NBA.
  auto* pre = sched.GetEventPool().Acquire();
  pre->kind = EventKind::kEvaluation;
  pre->callback = [&]() { order.push_back("pre_nba_rw"); };
  sched.ScheduleEvent({0}, Region::kPreNBA, pre);

  // cbReadWriteSynch in Post-NBA.
  auto* post = sched.GetEventPool().Acquire();
  post->kind = EventKind::kEvaluation;
  post->callback = [&]() { order.push_back("post_nba_rw"); };
  sched.ScheduleEvent({0}, Region::kPostNBA, post);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "pre_nba_rw");
  EXPECT_EQ(order[2], "nba");
  EXPECT_EQ(order[3], "post_nba_rw");
}

// ---------------------------------------------------------------------------
// Table 4-1: cbAtEndOfSimTime → Pre-Postponed
// A cbAtEndOfSimTime callback fires in the Pre-Postponed region, after all
// iterative regions (Active through ReNBA) and before the Postponed region.
// ---------------------------------------------------------------------------
TEST(SimCh410, CbAtEndOfSimTimeInPrePostponed) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* active = sched.GetEventPool().Acquire();
  active->kind = EventKind::kEvaluation;
  active->callback = [&]() { order.push_back("active"); };
  sched.ScheduleEvent({0}, Region::kActive, active);

  // cbAtEndOfSimTime → Pre-Postponed.
  auto* cb = sched.GetEventPool().Acquire();
  cb->kind = EventKind::kEvaluation;
  cb->callback = [&]() { order.push_back("pre_postponed_cb"); };
  sched.ScheduleEvent({0}, Region::kPrePostponed, cb);

  // A Postponed event for comparison.
  auto* postponed = sched.GetEventPool().Acquire();
  postponed->kind = EventKind::kEvaluation;
  postponed->callback = [&]() { order.push_back("postponed"); };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "pre_postponed_cb");
  EXPECT_EQ(order[2], "postponed");
}

// ---------------------------------------------------------------------------
// Table 4-1: cbReadOnlySynch → Postponed
// A cbReadOnlySynch callback fires in the Postponed region, the very last
// region in a time step. This region is read-only — no new events may be
// scheduled that would cause the current time step to iterate.
// ---------------------------------------------------------------------------
TEST(SimCh410, CbReadOnlySynchInPostponed) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* active = sched.GetEventPool().Acquire();
  active->kind = EventKind::kEvaluation;
  active->callback = [&]() { order.push_back("active"); };
  sched.ScheduleEvent({0}, Region::kActive, active);

  // cbReadOnlySynch → Postponed.
  auto* cb = sched.GetEventPool().Acquire();
  cb->kind = EventKind::kEvaluation;
  cb->callback = [&]() { order.push_back("postponed_cb"); };
  sched.ScheduleEvent({0}, Region::kPostponed, cb);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "postponed_cb");
}

// Helper: schedule an evaluation event that appends a label to an order log.
static void ScheduleOrderEvent(Scheduler& sched, SimTime time, Region region,
                               std::vector<std::string>& order,
                               const std::string& label) {
  auto* ev = sched.GetEventPool().Acquire();
  ev->kind = EventKind::kEvaluation;
  ev->callback = [&order, label]() { order.push_back(label); };
  sched.ScheduleEvent(time, region, ev);
}

// ---------------------------------------------------------------------------
// §4.10 Table 4-1: Full region ordering of PLI callbacks
// Verifies the complete ordering of all PLI callback regions within a single
// time step: Pre-Active → Active → Pre-NBA → NBA → Post-NBA →
// Pre-Postponed → Postponed.
// ---------------------------------------------------------------------------
TEST(SimCh410, FullPliCallbackRegionOrdering) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Pre-Active (cbAfterDelay / cbNextSimTime / cbAtStartOfSimTime).
  ScheduleOrderEvent(sched, SimTime{0}, Region::kPreActive, order,
                     "pre_active");

  // Active (user logic) — schedules NBA from within its callback.
  auto* active = sched.GetEventPool().Acquire();
  active->kind = EventKind::kEvaluation;
  active->callback = [&]() {
    order.push_back("active");
    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&order]() { order.push_back("nba"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  // Pre-NBA (cbNBASynch / cbReadWriteSynch).
  ScheduleOrderEvent(sched, SimTime{0}, Region::kPreNBA, order, "pre_nba");
  // Post-NBA (cbReadWriteSynch).
  ScheduleOrderEvent(sched, SimTime{0}, Region::kPostNBA, order, "post_nba");
  // Pre-Postponed (cbAtEndOfSimTime).
  ScheduleOrderEvent(sched, SimTime{0}, Region::kPrePostponed, order,
                     "pre_postponed");
  // Postponed (cbReadOnlySynch).
  ScheduleOrderEvent(sched, SimTime{0}, Region::kPostponed, order, "postponed");

  sched.Run();
  const std::vector<std::string> kExpected = {
      "pre_active", "active",        "pre_nba",  "nba",
      "post_nba",   "pre_postponed", "postponed"};
  EXPECT_EQ(order, kExpected);
}
