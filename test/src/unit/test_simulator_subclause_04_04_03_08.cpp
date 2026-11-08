#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_region_callback.h"
#include "helpers_scheduler_event.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"

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
  EXPECT_TRUE(IsPliRegion(Region::kPostReNBA));
}

TEST(PliPostReNbaSim, PostReNBAReadsValueFromRealNonblockingAssign) {
  SimFixture f;
  ExpectRegionCallbackReads(f,
                            "module t;\n"
                            "  logic [7:0] q;\n"
                            "  initial q <= 8'd42;\n"
                            "endmodule\n",
                            Region::kPostReNBA, "q", 42u);
}

TEST(PliPostReNbaSim, PostReNBAReadsValueSettledByReactiveNonblockingAssign) {
  SimFixture f;
  ExpectRegionCallbackReads(f,
                            "module t;\n"
                            "  logic [7:0] q;\n"
                            "  program p;\n"
                            "    initial q <= 8'd42;\n"
                            "  endprogram\n"
                            "endmodule\n",
                            Region::kPostReNBA, "q", 42u);
}
