#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler_event.h"
#include "helpers_zero_delay_route.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

TEST(ReInactiveRegionSim, ReInactiveExecutesAfterReactive) {
  VerifyTwoRegionOrder({Region::kReactive, "reactive"},
                       {Region::kReInactive, "reinactive"});
}

TEST(ReInactiveRegionSim, ReactivesScheduledDuringDrainRunBeforeReInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* react1 = sched.GetEventPool().Acquire();
  react1->callback = [&]() {
    order.push_back("reactive1");
    auto* react2 = sched.GetEventPool().Acquire();
    react2->callback = [&]() { order.push_back("reactive2"); };
    sched.ScheduleEvent({0}, Region::kReactive, react2);
  };
  sched.ScheduleEvent({0}, Region::kReactive, react1);

  auto* reinactive = sched.GetEventPool().Acquire();
  reinactive->callback = [&]() { order.push_back("reinactive"); };
  sched.ScheduleEvent({0}, Region::kReInactive, reinactive);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "reactive1");
  EXPECT_EQ(order[1], "reactive2");
  EXPECT_EQ(order[2], "reinactive");
}

TEST(ReInactiveRegionSim, ChainedZeroDelayIteration) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto log_reinactive2 = [&order]() { order.push_back("reinactive2"); };
  auto do_reactive2 = [&]() {
    order.push_back("reactive2");
    auto* reinact2 = sched.GetEventPool().Acquire();
    reinact2->callback = log_reinactive2;
    sched.ScheduleEvent({0}, Region::kReInactive, reinact2);
  };

  auto do_reinactive1 = [&]() {
    order.push_back("reinactive1");
    auto* react2 = sched.GetEventPool().Acquire();
    react2->callback = do_reactive2;
    sched.ScheduleEvent({0}, Region::kReactive, react2);
  };

  auto* react1 = sched.GetEventPool().Acquire();
  react1->callback = [&]() {
    order.push_back("reactive1");
    auto* reinact1 = sched.GetEventPool().Acquire();
    reinact1->callback = do_reinactive1;
    sched.ScheduleEvent({0}, Region::kReInactive, reinact1);
  };
  sched.ScheduleEvent({0}, Region::kReactive, react1);

  sched.Run();
  std::vector<std::string> expected = {"reactive1", "reinactive1", "reactive2",
                                       "reinactive2"};
  EXPECT_EQ(order, expected);
}

TEST(ReInactiveRegionSim, ReInactiveExecutesBeforeReNBA) {
  VerifyTwoRegionOrder({Region::kReInactive, "reinactive"},
                       {Region::kReNBA, "renba"});
}

TEST(ReInactiveRegionSim, ReInactiveEventsAcrossMultipleTimeSlots) {
  VerifyEventsAcrossTimeSlots(Region::kReInactive);
}

TEST(ReInactiveRegionSim, ReInactiveRegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kReInactive, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(ReInactiveRegionSim, ReInactiveIsReactiveSetDualOfInactive) {
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kInactive),
            Region::kReInactive);
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kReInactive), Region::kCOUNT);

  EXPECT_TRUE(IsActiveRegionSet(Region::kInactive));
  EXPECT_TRUE(IsReactiveRegionSet(Region::kReInactive));
}

TEST(ReInactiveRegionSim,
     ZeroDelayFromReactiveContextRoutesToReInactiveAndResumesInSameSlot) {
  SimFixture f;
  RunZeroDelayRouteScenario(f,
                            "module top;\n"
                            "  logic [7:0] b, snap, done;\n"
                            "  program p;\n"
                            "    initial begin\n"
                            "      b = 8'd0;\n"
                            "      snap = 8'd0;\n"
                            "      b <= 8'd9;\n"
                            "      done = #0 8'd1;\n"
                            "      snap = b;\n"
                            "    end\n"
                            "  endprogram\n"
                            "endmodule\n",
                            9u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

TEST(ReInactiveRegionSim,
     ZeroDelayFromReactiveContextYieldsToOtherReactiveProcessBeforeResuming) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] shared, seen;\n"
      "  program p;\n"
      "    initial begin\n"
      "      seen = 8'd0;\n"
      "      #0;\n"
      "      seen = shared;\n"
      "    end\n"
      "    initial begin\n"
      "      shared = 8'd42;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("seen")->value.ToUint64(), 42u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

TEST(ReInactiveRegionSim,
     NonzeroDelayFromReactiveContextAdvancesTimeInsteadOfReInactiveResume) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] snap;\n"
      "  program p;\n"
      "    initial begin\n"
      "      snap = 8'd0;\n"
      "      #1;\n"
      "      snap = 8'd7;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("snap")->value.ToUint64(), 7u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 1u);
}

TEST(ReInactiveRegionSim,
     IntraAssignmentZeroDelayFromReactiveContextYieldsBeforeResuming) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] shared, seen, done;\n"
      "  program p;\n"
      "    initial begin\n"
      "      seen = 8'd0;\n"
      "      done = #0 8'd1;\n"
      "      seen = shared;\n"
      "    end\n"
      "    initial begin\n"
      "      shared = 8'd42;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("done")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("seen")->value.ToUint64(), 42u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

TEST(ReInactiveRegionSim,
     ReInactiveEventWaitsForReactiveEventsCreatedMeanwhile) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;
  auto* first = sched.GetEventPool().Acquire();
  first->callback = [&]() {
    order.push_back("reinactive1");
    auto* reactive = sched.GetEventPool().Acquire();
    reactive->callback = [&]() { order.push_back("reactive"); };
    sched.ScheduleEvent({0}, Region::kReactive, reactive);
    auto* second = sched.GetEventPool().Acquire();
    second->callback = [&]() { order.push_back("reinactive2"); };
    sched.ScheduleEvent({0}, Region::kReInactive, second);
  };
  sched.ScheduleEvent({0}, Region::kReInactive, first);
  sched.Run();
  EXPECT_EQ(order, (std::vector<std::string>{"reinactive1", "reactive",
                                             "reinactive2"}));
}
