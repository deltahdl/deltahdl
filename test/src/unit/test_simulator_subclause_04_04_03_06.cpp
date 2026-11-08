#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler_event.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

TEST(PliPostObservedSim, PostObservedCanReadValues) {
  VerifyRegionCanReadActiveValue(Region::kPostObserved);
}

TEST(PliPostObservedSim, PostObservedExecutesAfterObservedBeforeReactive) {
  VerifyThreeRegionOrder({Region::kObserved, "observed"},
                         {Region::kPostObserved, "post_observed"},
                         {Region::kReactive, "reactive"});
}

TEST(PliPostObservedSim, PostObservedIsClassifiedAsPliRegion) {
  EXPECT_TRUE(IsPliRegion(Region::kPostObserved));
}

TEST(PliPostObservedSim, PostObservedRegionHoldsMultiplePLICallbacks) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPostObserved, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(PliPostObservedSim, PostObservedEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kPostObserved, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

TEST(PliPostObservedSim, PostObservedProvidesReadOnlySnapshotAfterObserved) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;
  int sum_in_post_observed = -1;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    a = 10;
    b = 20;
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* observed = sched.GetEventPool().Acquire();
  observed->callback = [&]() { b = 30; };
  sched.ScheduleEvent({0}, Region::kObserved, observed);

  auto* post_obs = sched.GetEventPool().Acquire();
  post_obs->callback = [&]() { sum_in_post_observed = a + b; };
  sched.ScheduleEvent({0}, Region::kPostObserved, post_obs);

  sched.Run();
  EXPECT_EQ(sum_in_post_observed, 40);
}

TEST(PliPostObservedSim, PostObservedReadsValueFromRealNonblockingAssign) {
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
  uint64_t post_observed_sample = 0;
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&]() {
    ran = true;
    post_observed_sample = f.ctx.FindVariable("q")->value.ToUint64();
  };
  f.scheduler.ScheduleEvent({0}, Region::kPostObserved, ev);

  f.scheduler.Run();
  EXPECT_TRUE(ran);
  EXPECT_EQ(post_observed_sample, 42u);
}

TEST(PliPostObservedSim, PostObservedInfrastructureWorksEvenIfCurrentlyUnused) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kReactive, "reactive", order);
  ScheduleLabeled(sched, Region::kPostObserved, "post_observed", order);
  ScheduleLabeled(sched, Region::kObserved, "observed", order);
  ScheduleLabeled(sched, Region::kPreObserved, "pre_observed", order);
  ScheduleLabeled(sched, Region::kPostNBA, "post_nba", order);
  ScheduleLabeled(sched, Region::kActive, "active", order);

  sched.Run();
  std::vector<std::string> expected = {"active",        "post_nba",
                                       "pre_observed",  "observed",
                                       "post_observed", "reactive"};
  EXPECT_EQ(order, expected);
}
