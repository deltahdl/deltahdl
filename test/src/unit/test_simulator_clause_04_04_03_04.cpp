#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
// coverage.h must precede fixture_simulator.h: the latter pulls in
// sim_context.h, whose inline constructor holds a unique_ptr<CoverageDB> and so
// needs the complete CoverageDB type visible at parse time.
#include "fixture_simulator.h"
#include "helpers_scheduler_event.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

TEST(PliPostNbaSim, PostNBACanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { value = 42; };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPostNBA, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

TEST(PliPostNbaSim, PostNBACanWriteValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled_in_observed = -1;

  auto* post_nba = sched.GetEventPool().Acquire();
  post_nba->callback = [&]() { value = 99; };
  sched.ScheduleEvent({0}, Region::kPostNBA, post_nba);

  auto* observed = sched.GetEventPool().Acquire();
  observed->callback = [&]() { sampled_in_observed = value; };
  sched.ScheduleEvent({0}, Region::kObserved, observed);

  sched.Run();
  EXPECT_EQ(sampled_in_observed, 99);
}

TEST(PliPostNbaSim, PostNBACanCreateEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* post_nba = sched.GetEventPool().Acquire();
  post_nba->callback = [&]() {
    order.push_back("post_nba");

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

TEST(PliPostNbaSim, PostNBAExecutesAfterNBABeforePreObserved) {
  VerifyThreeRegionOrder({Region::kNBA, "nba"}, {Region::kPostNBA, "post_nba"},
                         {Region::kPreObserved, "pre_observed"});
}

TEST(PliPostNbaSim, PostNBARegionHoldsMultiplePLICallbacks) {
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

TEST(PliPostNbaSim, PostNBAEventsAcrossMultipleTimeSlots) {
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

// Edge case: an event created from within a Post-NBA callback that lands back
// in the Post-NBA region of the same time slot must still be evaluated, and
// still only after the NBA region has run. Exercises the scheduler draining the
// region to empty so the "create events after NBA" guarantee holds for
// re-entrant scheduling.
TEST(PliPostNbaSim, PostNBAReentrantEventStillRunsAfterNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { order.push_back("nba"); };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  auto* post_nba = sched.GetEventPool().Acquire();
  post_nba->callback = [&]() {
    order.push_back("post_nba");

    auto* again = sched.GetEventPool().Acquire();
    again->callback = [&order]() { order.push_back("post_nba_reentrant"); };
    sched.ScheduleEvent({0}, Region::kPostNBA, again);
  };
  sched.ScheduleEvent({0}, Region::kPostNBA, post_nba);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "nba");
  EXPECT_EQ(order[1], "post_nba");
  EXPECT_EQ(order[2], "post_nba_reentrant");
}

// End-to-end coverage of the "after the NBA region is evaluated" guarantee,
// building the consumed NBA update from the dependency §4.4.2.4's real source
// syntax: a nonblocking assignment. Parsing/elaborating/lowering `q <= 42`
// schedules q's update into the real NBA region at time 0. A Post-NBA callback
// registered in that same slot (the only way PLI code reaches this region -
// there is no HDL syntax for it) must sample the value the NBA update wrote,
// which can only be true if the Post-NBA region drains after NBA. Driving the
// whole pipeline - not a hand-built NBA event - is what ties the ordering rule
// to a genuine nonblocking-assignment update.
TEST(PliPostNbaSim, PostNBAReadsValueFromRealNonblockingAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  initial q <= 8'd42;\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(f.has_errors);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  bool ran = false;
  uint64_t post_nba_sample = 0;
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&]() {
    ran = true;
    post_nba_sample = f.ctx.FindVariable("q")->value.ToUint64();
  };
  f.scheduler.ScheduleEvent({0}, Region::kPostNBA, ev);

  f.scheduler.Run();
  EXPECT_TRUE(ran);
  EXPECT_EQ(post_nba_sample, 42u);
}
