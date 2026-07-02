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

// D2 input form: two nonblocking assignments issued together in the active set.
// Each samples its right-hand side immediately but defers the write into the
// NBA region, so the pair exchanges values. A blocking read-after-write would
// instead leave both variables holding the first source's value.
TEST(NbaRegionSim, NonblockingAssignPairSwapsThroughNBARegion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    a <= b;\n"
      "    b <= a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 20u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 10u);
}

// End-to-end observation of D1 ("NBA runs after all Inactive events") built
// from the §4.4.2.3 dependency's real `#0` syntax rather than kernel-scheduled
// events. The process schedules an NBA update, then an explicit `#0` suspends
// it into the Inactive region and resumes it within the same time slot. The
// read that follows the resume therefore still sees the pre-update value,
// proving the NBA region has not yet run when the Inactive-resumed code
// executes.
TEST(NbaRegionSim, NBAUpdateAppliesAfterZeroDelayInactiveResume) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] obs;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    a <= 8'd99;\n"
      "    #0;\n"
      "    obs = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // The Inactive-resumed read happened before the NBA update landed.
  EXPECT_EQ(f.ctx.FindVariable("obs")->value.ToUint64(), 1u);
  // The NBA update did eventually apply once the region ran.
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 99u);
}
