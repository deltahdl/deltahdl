#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.9.4 Nonblocking assignment
//
// LRM §4.9.4:
//   "A nonblocking assignment statement (see 10.4.2) always computes the
//    updated value and schedules the update as an NBA update event, either
//    in the current time step if the delay is zero or as a future event if
//    the delay is nonzero. The values in effect when the update is placed
//    in the event region are used to compute both the right-hand value and
//    the left-hand target."
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.9.4 "always computes the updated value"
// The RHS of a nonblocking assignment is always evaluated to produce the
// updated value before the NBA event is scheduled.
// ---------------------------------------------------------------------------
TEST(SimCh4094, AlwaysComputesUpdatedValue) {
  Arena arena;
  Scheduler sched(arena);
  int src = 42;
  int dst = 0;

  // Model: dst <= src;  (src=42 at evaluation time)
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int rhs_val = src;  // Compute the updated value.
    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&, rhs_val]() { dst = rhs_val; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(dst, 42);
}

// ---------------------------------------------------------------------------
// §4.9.4 "schedules the update as an NBA update event"
// The update from a nonblocking assignment is scheduled in the NBA region,
// not the Active or Inactive region.
// ---------------------------------------------------------------------------
TEST(SimCh4094, SchedulesUpdateAsNbaEvent) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Schedule an NBA update and an Active update at the same time.
  // The Active update must execute before the NBA update.
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    // NBA update.
    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&]() { order.push_back("nba_update"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);

    // Active update (should execute before NBA).
    auto* active = sched.GetEventPool().Acquire();
    active->kind = EventKind::kUpdate;
    active->callback = [&]() { order.push_back("active_update"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, active);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "active_update");
  EXPECT_EQ(order[1], "nba_update");
}

// ---------------------------------------------------------------------------
// §4.9.4 "either in the current time step if the delay is zero"
// A nonblocking assignment with zero delay schedules the NBA event in the
// current time step's NBA region.
// ---------------------------------------------------------------------------
TEST(SimCh4094, ZeroDelaySchedulesNbaInCurrentTimestep) {
  Arena arena;
  Scheduler sched(arena);
  int dst = 0;
  bool nba_executed_at_time_zero = false;

  // Model: dst <= #0 5;
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int rhs_val = 5;
    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&, rhs_val]() {
      dst = rhs_val;
      nba_executed_at_time_zero = (sched.CurrentTime().ticks == 0);
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(dst, 5);
  EXPECT_TRUE(nba_executed_at_time_zero);
}

// ---------------------------------------------------------------------------
// §4.9.4 "or as a future event if the delay is nonzero"
// A nonblocking assignment with a nonzero delay schedules the NBA event at
// the future time.
// ---------------------------------------------------------------------------
TEST(SimCh4094, NonzeroDelaySchedulesNbaAsFutureEvent) {
  Arena arena;
  Scheduler sched(arena);
  int dst = 0;
  uint64_t nba_time = 0;

  // Model: dst <= #10 99;
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int rhs_val = 99;
    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&, rhs_val]() {
      dst = rhs_val;
      nba_time = sched.CurrentTime().ticks;
    };
    sched.ScheduleEvent({10}, Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(dst, 99);
  EXPECT_EQ(nba_time, 10u);
}

// ---------------------------------------------------------------------------
// §4.9.4 "The values in effect when the update is placed in the event region
//          are used to compute...the right-hand value"
// The RHS is computed using values at the time the NBA is scheduled, not at
// the time the NBA executes. If the source changes after scheduling, the
// original captured value is used.
// ---------------------------------------------------------------------------
TEST(SimCh4094, RhsComputedAtScheduleTime) {
  Arena arena;
  Scheduler sched(arena);
  int src = 10;
  int dst = 0;

  // Model: dst <= src; at time 0 when src=10.
  // src changes later but dst should get the captured value 10.
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int rhs_val = src;  // Capture RHS now (src=10).
    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&, rhs_val]() { dst = rhs_val; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
    // Change src after scheduling the NBA but before it executes.
    src = 99;
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  // dst should be 10 (value when NBA was placed), not 99.
  EXPECT_EQ(dst, 10);
}

// ---------------------------------------------------------------------------
// §4.9.4 "and the left-hand target"
// The LHS target is also determined using values at the time the NBA is
// scheduled, not at the time it executes.
// ---------------------------------------------------------------------------
TEST(SimCh4094, LhsTargetDeterminedAtScheduleTime) {
  Arena arena;
  Scheduler sched(arena);
  int select = 0;
  int dst_a = 0;
  int dst_b = 0;

  // Model: (select ? dst_b : dst_a) <= 1;
  // At time 0, select=0 → target is dst_a. Target is captured at schedule
  // time, so even if select changes before the NBA executes, dst_a is used.
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int target_select = select;  // Capture target at schedule time.
    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&, target_select]() {
      if (target_select == 0) {
        dst_a = 1;
      } else {
        dst_b = 1;
      }
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
    // Change select after scheduling, before NBA executes.
    select = 1;
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  // Target was dst_a (select=0 at schedule time), not dst_b.
  EXPECT_EQ(dst_a, 1);
  EXPECT_EQ(dst_b, 0);
}

// ---------------------------------------------------------------------------
// §4.9.4 "schedules the update as an NBA update event"
// Multiple nonblocking assignments from the same process all schedule their
// updates in the NBA region. All NBA updates execute after Active completes.
// ---------------------------------------------------------------------------
TEST(SimCh4094, MultipleNbasAllScheduleInNbaRegion) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;
  int c = 0;

  // Model: a <= 1; b <= 2; c <= 3;
  // All three NBAs schedule in NBA region and all execute.
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    auto* nba1 = sched.GetEventPool().Acquire();
    nba1->kind = EventKind::kUpdate;
    nba1->callback = [&]() { a = 1; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba1);

    auto* nba2 = sched.GetEventPool().Acquire();
    nba2->kind = EventKind::kUpdate;
    nba2->callback = [&]() { b = 2; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba2);

    auto* nba3 = sched.GetEventPool().Acquire();
    nba3->kind = EventKind::kUpdate;
    nba3->callback = [&]() { c = 3; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba3);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(a, 1);
  EXPECT_EQ(b, 2);
  EXPECT_EQ(c, 3);
}

// ---------------------------------------------------------------------------
// §4.9.4 "always computes the updated value and schedules the update"
// The nonblocking assignment does NOT block the executing process. The process
// continues immediately after scheduling the NBA event.
// ---------------------------------------------------------------------------
TEST(SimCh4094, NbaDoesNotBlockProcess) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Model: begin dst <= 1; next_stmt; end
  // The process schedules the NBA and immediately continues to next_stmt.
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    order.push_back("before_nba");
    // Schedule NBA (does not block).
    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&]() { order.push_back("nba_update"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
    // Process continues immediately.
    order.push_back("after_nba_next_stmt");
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "before_nba");
  EXPECT_EQ(order[1], "after_nba_next_stmt");
  EXPECT_EQ(order[2], "nba_update");
}

// ---------------------------------------------------------------------------
// §4.9.4 "schedules the update as an NBA update event"
// NBA events execute after all Active and Inactive events in the same time
// step, demonstrating the stratified region ordering.
// ---------------------------------------------------------------------------
TEST(SimCh4094, NbaExecutesAfterActiveAndInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    // Schedule an Inactive event.
    auto* inactive = sched.GetEventPool().Acquire();
    inactive->kind = EventKind::kUpdate;
    inactive->callback = [&]() { order.push_back("inactive"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kInactive, inactive);

    // Schedule an NBA event.
    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&]() { order.push_back("nba"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);

    order.push_back("active");
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "inactive");
  EXPECT_EQ(order[2], "nba");
}

// ---------------------------------------------------------------------------
// §4.9.4 "always computes the updated value and schedules the update as an
//          NBA update event"
// Classic swap pattern: two nonblocking assignments to swap values. Both RHS
// values are computed before either NBA update executes.
// ---------------------------------------------------------------------------
TEST(SimCh4094, SwapPatternBothRhsComputedBeforeUpdate) {
  Arena arena;
  Scheduler sched(arena);
  int x = 1;
  int y = 2;

  // Model: x <= y; y <= x;
  // Both RHS values (y=2, x=1) captured before either NBA executes.
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int rhs_x = y;  // Capture y=2 for x.
    int rhs_y = x;  // Capture x=1 for y.

    auto* nba1 = sched.GetEventPool().Acquire();
    nba1->kind = EventKind::kUpdate;
    nba1->callback = [&, rhs_x]() { x = rhs_x; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba1);

    auto* nba2 = sched.GetEventPool().Acquire();
    nba2->kind = EventKind::kUpdate;
    nba2->callback = [&, rhs_y]() { y = rhs_y; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba2);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  // After swap: x=2, y=1.
  EXPECT_EQ(x, 2);
  EXPECT_EQ(y, 1);
}
