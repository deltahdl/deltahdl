#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
// coverage.h must precede fixture_simulator.h: the latter pulls in
// sim_context.h, whose inline destructor holds a unique_ptr<CoverageDB> and so
// needs the complete CoverageDB type visible at parse time.
#include "simulator/coverage.h"
// clang-format off
#include "fixture_simulator.h"
// clang-format on
#include "helpers_scheduler_event.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

TEST(PliPostReNbaSim, PostReNBACanReadValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  auto* re_nba = sched.GetEventPool().Acquire();
  re_nba->callback = [&]() { value = 42; };
  sched.ScheduleEvent({0}, Region::kReNBA, re_nba);

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPostReNBA, ev);

  sched.Run();
  EXPECT_EQ(sampled, 42);
}

TEST(PliPostReNbaSim, PostReNBACanWriteValues) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled_in_pre_postponed = -1;

  auto* post_re_nba = sched.GetEventPool().Acquire();
  post_re_nba->callback = [&]() { value = 99; };
  sched.ScheduleEvent({0}, Region::kPostReNBA, post_re_nba);

  auto* pre_postponed = sched.GetEventPool().Acquire();
  pre_postponed->callback = [&]() { sampled_in_pre_postponed = value; };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pre_postponed);

  sched.Run();
  EXPECT_EQ(sampled_in_pre_postponed, 99);
}

TEST(PliPostReNbaSim, PostReNBACanCreateEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* post_re_nba = sched.GetEventPool().Acquire();
  post_re_nba->callback = [&]() {
    order.push_back("post_re_nba");

    auto* new_ev = sched.GetEventPool().Acquire();
    new_ev->callback = [&order]() { order.push_back("created_pre_postponed"); };
    sched.ScheduleEvent({0}, Region::kPrePostponed, new_ev);
  };
  sched.ScheduleEvent({0}, Region::kPostReNBA, post_re_nba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "post_re_nba");
  EXPECT_EQ(order[1], "created_pre_postponed");
}

TEST(PliPostReNbaSim, PostReNBAExecutesAfterReNBABeforePrePostponed) {
  VerifyThreeRegionOrder({Region::kReNBA, "re_nba"},
                         {Region::kPostReNBA, "post_re_nba"},
                         {Region::kPrePostponed, "pre_postponed"});
}

TEST(PliPostReNbaSim, PostReNBARegionHoldsMultiplePLICallbacks) {
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

TEST(PliPostReNbaSim, PostReNBAEventsAcrossMultipleTimeSlots) {
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

TEST(PliPostReNbaSim, PostReNBAIsClassifiedAsPliRegion) {
  // §4.4.3.8 establishes Post-Re-NBA as a PLI callback control point; the
  // scheduler encodes that membership in IsPliRegion.
  EXPECT_TRUE(IsPliRegion(Region::kPostReNBA));
}

// End-to-end coverage of §4.4.3.8's read guarantee, building the consumed value
// from real source syntax rather than a hand-scheduled event. §4.4.3.8 lets a
// Post-Re-NBA PLI callback read values after the Re-NBA region is evaluated;
// because Post-Re-NBA runs late in the time slot, a value settled by an earlier
// region is still visible when it fires. Parsing/elaborating/lowering
// `q <= 8'd42` schedules q's update into the real NBA region at time 0. A
// Post-Re-NBA callback in that same slot (the only way PLI code reaches this
// region - there is no HDL syntax for it) must observe the value that genuine
// nonblocking assignment wrote, which holds only if the scheduler drives every
// intervening region through Post-Re-NBA before the callback runs. Driving the
// whole pipeline - not a hand-built NBA event - ties the read rule to a real
// nonblocking assignment.
TEST(PliPostReNbaSim, PostReNBAReadsValueFromRealNonblockingAssign) {
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
  uint64_t post_re_nba_sample = 0;
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&]() {
    ran = true;
    post_re_nba_sample = f.ctx.FindVariable("q")->value.ToUint64();
  };
  f.scheduler.ScheduleEvent({0}, Region::kPostReNBA, ev);

  f.scheduler.Run();
  EXPECT_TRUE(ran);
  EXPECT_EQ(post_re_nba_sample, 42u);
}

// End-to-end coverage of §4.4.3.8's read guarantee built from the Re-NBA region
// dependency's (§4.4.2.8) own real syntax. Re-NBA is the reactive-region-set
// dual of NBA: a nonblocking assignment executed by a program's reactive
// process schedules its update into Re-NBA, not into the active-set NBA region.
// Lowering a program-block `q <= 8'd42` therefore produces a genuine Re-NBA
// event at time 0. §4.4.3.8 says a Post-Re-NBA callback reads values after
// Re-NBA is evaluated, so a callback in that same slot must observe the value
// the reactive nonblocking assignment settled - which holds only if the
// scheduler drains Re-NBA before Post-Re-NBA. Driving the whole pipeline - not
// a hand-scheduled Re-NBA event - ties the read rule to a real reactive
// nonblocking update.
TEST(PliPostReNbaSim, PostReNBAReadsValueSettledByReactiveNonblockingAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  program p;\n"
      "    initial q <= 8'd42;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(f.has_errors);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  bool ran = false;
  uint64_t post_re_nba_sample = 0;
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&]() {
    ran = true;
    post_re_nba_sample = f.ctx.FindVariable("q")->value.ToUint64();
  };
  f.scheduler.ScheduleEvent({0}, Region::kPostReNBA, ev);

  f.scheduler.Run();
  EXPECT_TRUE(ran);
  EXPECT_EQ(post_re_nba_sample, 42u);
}
