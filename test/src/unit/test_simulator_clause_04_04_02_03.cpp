#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler_event.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

using namespace delta;

TEST(InactiveRegionSim, InactiveExecutesAfterActive) {
  VerifyTwoRegionOrder({Region::kActive, "active"},
                       {Region::kInactive, "inactive"});
}

TEST(InactiveRegionSim, AllActiveEventsCompleteBeforeInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  for (int i = 0; i < 3; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() {
      order.push_back("active" + std::to_string(i));
    };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  auto* inactive = sched.GetEventPool().Acquire();
  inactive->callback = [&]() { order.push_back("inactive"); };
  sched.ScheduleEvent({0}, Region::kInactive, inactive);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);

  EXPECT_EQ(order[3], "inactive");
}

TEST(InactiveRegionSim, ActivesScheduledDuringDrainRunBeforeInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* act1 = sched.GetEventPool().Acquire();
  act1->callback = [&]() {
    order.push_back("active1");
    auto* act2 = sched.GetEventPool().Acquire();
    act2->callback = [&]() { order.push_back("active2"); };
    sched.ScheduleEvent({0}, Region::kActive, act2);
  };
  sched.ScheduleEvent({0}, Region::kActive, act1);

  auto* inactive = sched.GetEventPool().Acquire();
  inactive->callback = [&]() { order.push_back("inactive"); };
  sched.ScheduleEvent({0}, Region::kInactive, inactive);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "active1");
  EXPECT_EQ(order[1], "active2");
  EXPECT_EQ(order[2], "inactive");
}

TEST(InactiveRegionSim, InactiveToActiveIteration) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* act1 = sched.GetEventPool().Acquire();
  act1->callback = [&]() {
    order.push_back("active1");
    auto* inact = sched.GetEventPool().Acquire();
    inact->callback = [&]() {
      order.push_back("inactive");

      auto* act2 = sched.GetEventPool().Acquire();
      act2->callback = [&order]() { order.push_back("active2"); };
      sched.ScheduleEvent({0}, Region::kActive, act2);
    };
    sched.ScheduleEvent({0}, Region::kInactive, inact);
  };
  sched.ScheduleEvent({0}, Region::kActive, act1);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "active1");
  EXPECT_EQ(order[1], "inactive");
  EXPECT_EQ(order[2], "active2");
}

TEST(InactiveRegionSim, ChainedZeroDelayIteration) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto log_inactive2 = [&order]() { order.push_back("inactive2"); };
  auto do_active2 = [&]() {
    order.push_back("active2");
    auto* inact2 = sched.GetEventPool().Acquire();
    inact2->callback = log_inactive2;
    sched.ScheduleEvent({0}, Region::kInactive, inact2);
  };

  auto do_inactive1 = [&]() {
    order.push_back("inactive1");
    auto* act2 = sched.GetEventPool().Acquire();
    act2->callback = do_active2;
    sched.ScheduleEvent({0}, Region::kActive, act2);
  };

  auto* act1 = sched.GetEventPool().Acquire();
  act1->callback = [&]() {
    order.push_back("active1");
    auto* inact1 = sched.GetEventPool().Acquire();
    inact1->callback = do_inactive1;
    sched.ScheduleEvent({0}, Region::kInactive, inact1);
  };
  sched.ScheduleEvent({0}, Region::kActive, act1);

  sched.Run();
  std::vector<std::string> expected = {"active1", "inactive1", "active2",
                                       "inactive2"};
  EXPECT_EQ(order, expected);
}

TEST(InactiveRegionSim, InactiveExecutesBeforeNBA) {
  VerifyTwoRegionOrder({Region::kInactive, "inactive"}, {Region::kNBA, "nba"});
}

TEST(InactiveRegionSim, InactiveEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kInactive, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

TEST(InactiveRegionSim, InactiveExecutesBeforeReInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto* ev_inactive = sched.GetEventPool().Acquire();
  ev_inactive->callback = [&order]() { order.push_back(1); };
  sched.ScheduleEvent({0}, Region::kInactive, ev_inactive);

  auto* ev_reinactive = sched.GetEventPool().Acquire();
  ev_reinactive->callback = [&order]() { order.push_back(2); };
  sched.ScheduleEvent({0}, Region::kReInactive, ev_reinactive);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
}

TEST(InactiveRegionSim, InactiveRegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kInactive, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

// §4.4.2.3: an explicit #0 suspends the running process into the Inactive
// region so that every other Active event of the current time slot drains
// before it resumes in the next Inactive->Active iteration. The reader initial
// is declared first, so it activates first (declaration-order FIFO in the
// Active region); its #0 must let the later writer initial run before the read
// is observed. A no-op #0 would read the pre-write value instead, so `seen`
// distinguishes the two.
TEST(InactiveRegionSim, ZeroDelayYieldsToOtherActiveProcessesBeforeResuming) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] shared, seen;\n"
      "  initial begin\n"
      "    seen = 8'd0;\n"
      "    #0;\n"
      "    seen = shared;\n"
      "  end\n"
      "  initial begin\n"
      "    shared = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("seen")->value.ToUint64(), 42u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

// §4.4.2.3 negative/discriminating form: the Inactive-region resume is specific
// to an *explicit #0*. The closest input that must be handled differently is a
// nonzero delay, which suspends the process to a *later* time slot rather than
// the current slot's Inactive region. Here #1 must advance simulation time, so
// the post-delay write lands at time 1 -- an implementation that funneled every
// delay into the current-slot Inactive region (mistreating #1 as #0) would
// leave the clock at 0. Observing ticks==1 proves the rule keys on zero
// specifically.
TEST(InactiveRegionSim, NonzeroDelayAdvancesTimeInsteadOfInactiveResume) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] snap;\n"
      "  initial begin\n"
      "    snap = 8'd0;\n"
      "    #1;\n"
      "    snap = 8'd7;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("snap")->value.ToUint64(), 7u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 1u);
}
