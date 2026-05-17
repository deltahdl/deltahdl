#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler_event.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(NbaRegionSim, NBAExecutesAfterInactive) {
  VerifyTwoRegionOrder({Region::kInactive, "inactive"}, {Region::kNBA, "nba"});
}

TEST(NbaRegionSim, AllInactiveEventsCompleteBeforeNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  for (int i = 0; i < 3; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() {
      order.push_back("inactive" + std::to_string(i));
    };
    sched.ScheduleEvent({0}, Region::kInactive, ev);
  }

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { order.push_back("nba"); };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);

  EXPECT_EQ(order[3], "nba");
}

TEST(NbaRegionSim, InactivesScheduledDuringDrainRunBeforeNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* inact1 = sched.GetEventPool().Acquire();
  inact1->callback = [&]() {
    order.push_back("inactive1");
    auto* inact2 = sched.GetEventPool().Acquire();
    inact2->callback = [&]() { order.push_back("inactive2"); };
    sched.ScheduleEvent({0}, Region::kInactive, inact2);
  };
  sched.ScheduleEvent({0}, Region::kInactive, inact1);

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { order.push_back("nba"); };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "inactive1");
  EXPECT_EQ(order[1], "inactive2");
  EXPECT_EQ(order[2], "nba");
}

TEST(NbaRegionSim, NBAToActiveIteration) {
  VerifyIterationChain(Region::kActive, "active", Region::kNBA, "nba");
}

TEST(NbaRegionSim, NBAExecutesAfterActiveAndInactiveBeforeObserved) {
  VerifyFourRegionOrder({Region::kActive, "active"},
                        {Region::kInactive, "inactive"}, {Region::kNBA, "nba"},
                        {Region::kObserved, "observed"});
}

TEST(NbaRegionSim, NBAEventsAcrossMultipleTimeSlots) {
  VerifyEventsAcrossTimeSlots(Region::kNBA);
}

TEST(NbaRegionSim, NBAExecutesBeforeReNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto* ev_nba = sched.GetEventPool().Acquire();
  ev_nba->callback = [&order]() { order.push_back(1); };
  sched.ScheduleEvent({0}, Region::kNBA, ev_nba);

  auto* ev_renba = sched.GetEventPool().Acquire();
  ev_renba->callback = [&order]() { order.push_back(2); };
  sched.ScheduleEvent({0}, Region::kReNBA, ev_renba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
}

TEST(NbaRegionSim, NBARegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kNBA, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(NbaRegionSim, NonblockingAssignFromActiveSetSchedulesNBA) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = a + 8'd2;\n"
      "    a <= 8'd99;\n"
      "    a = a + 8'd5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 99u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 3u);
}

TEST(NbaRegionSim, NonblockingAssignWithDelaySchedulesNBALater) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] b;\n"
      "  initial b <= #5 8'd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 99u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 5u);
}
