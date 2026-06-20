#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler_event.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

TEST(ReNbaRegionSim, ReNBAExecutesAfterReInactive) {
  VerifyTwoRegionOrder({Region::kReInactive, "reinactive"},
                       {Region::kReNBA, "renba"});
}

TEST(ReNbaRegionSim, AllReInactiveEventsCompleteBeforeReNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  for (int i = 0; i < 3; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() {
      order.push_back("reinactive" + std::to_string(i));
    };
    sched.ScheduleEvent({0}, Region::kReInactive, ev);
  }

  auto* renba = sched.GetEventPool().Acquire();
  renba->callback = [&]() { order.push_back("renba"); };
  sched.ScheduleEvent({0}, Region::kReNBA, renba);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);

  EXPECT_EQ(order[3], "renba");
}

TEST(ReNbaRegionSim, ReNBAToReactiveIteration) {
  VerifyIterationChain(Region::kReactive, "reactive", Region::kReNBA, "renba");
}

TEST(ReNbaRegionSim, ReNBAExecutesAfterReactiveAndReInactiveBeforePostReNBA) {
  VerifyFourRegionOrder(
      {Region::kReactive, "reactive"}, {Region::kReInactive, "reinactive"},
      {Region::kReNBA, "renba"}, {Region::kPostReNBA, "post_renba"});
}

TEST(ReNbaRegionSim, ReNBAEventsAcrossMultipleTimeSlots) {
  VerifyEventsAcrossTimeSlots(Region::kReNBA);
}

TEST(ReNbaRegionSim, ReNBARegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kReNBA, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(ReNbaRegionSim, ReInactivesScheduledDuringDrainRunBeforeReNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* reinact1 = sched.GetEventPool().Acquire();
  reinact1->callback = [&]() {
    order.push_back("reinactive1");
    auto* reinact2 = sched.GetEventPool().Acquire();
    reinact2->callback = [&]() { order.push_back("reinactive2"); };
    sched.ScheduleEvent({0}, Region::kReInactive, reinact2);
  };
  sched.ScheduleEvent({0}, Region::kReInactive, reinact1);

  auto* renba = sched.GetEventPool().Acquire();
  renba->callback = [&]() { order.push_back("renba"); };
  sched.ScheduleEvent({0}, Region::kReNBA, renba);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "reinactive1");
  EXPECT_EQ(order[1], "reinactive2");
  EXPECT_EQ(order[2], "renba");
}

TEST(ReNbaRegionSim, NonblockingAssignFromReactiveSetSchedulesReNBA) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  program p;\n"
      "    initial begin\n"
      "      a = 8'd1;\n"
      "      b = a + 8'd2;\n"
      "      a <= 8'd99;\n"
      "      a = a + 8'd5;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 99u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 3u);
}

TEST(ReNbaRegionSim,
     NonblockingAssignFromReactiveSetWithDelaySchedulesReNBALater) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] b;\n"
      "  program p;\n"
      "    initial b <= #5 8'd99;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 99u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 5u);
}

TEST(ReNbaRegionSim, ReNBAIsReactiveSetDualOfNBA) {
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kNBA), Region::kReNBA);
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kReNBA), Region::kCOUNT);

  EXPECT_TRUE(IsActiveRegionSet(Region::kNBA));
  EXPECT_TRUE(IsReactiveRegionSet(Region::kReNBA));
}
