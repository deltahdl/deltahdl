#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_scheduler_event.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SchedulerOverviewSim, PostponedIsLastRegionInTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kPostponed, "postponed", order);
  ScheduleLabeled(sched, Region::kActive, "active", order);
  ScheduleLabeled(sched, Region::kReactive, "reactive", order);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[2], "postponed");
}

TEST(SchedulerOverviewSim, NBAExecutionOrderMatchesSourceOrder) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a <= 8'd0;\n"
      "    a <= 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result, 1u);
}

TEST(SchedulerOverviewSim, DeterministicSequentialWithinProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = a * 8'd2;\n"
      "    c = b + a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 20u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 30u);
}

TEST(SchedulerOverviewSim, ConcurrentWriteSameTimeSlotLastWriteWins) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd1;\n"
      "  initial x = 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  uint64_t val = var->value.ToUint64();
  EXPECT_TRUE(val == 1u || val == 2u);
}

TEST(SchedulerOverviewSim, ActiveRegionInterleavingIsPossible) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto* ev1 = sched.GetEventPool().Acquire();
  ev1->callback = [&order]() { order.push_back(1); };
  sched.ScheduleEvent({0}, Region::kActive, ev1);

  auto* ev2 = sched.GetEventPool().Acquire();
  ev2->callback = [&order]() { order.push_back(2); };
  sched.ScheduleEvent({0}, Region::kActive, ev2);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_TRUE((order[0] == 1 && order[1] == 2) ||
              (order[0] == 2 && order[1] == 1));
}

TEST(SchedulerOverviewSim, PLIRegionsExistInEnum) {
  EXPECT_LT(static_cast<int>(Region::kPreActive),
            static_cast<int>(Region::kActive));
  EXPECT_LT(static_cast<int>(Region::kPreNBA), static_cast<int>(Region::kNBA));
  EXPECT_GT(static_cast<int>(Region::kPostNBA), static_cast<int>(Region::kNBA));
  EXPECT_LT(static_cast<int>(Region::kPreObserved),
            static_cast<int>(Region::kObserved));
  EXPECT_GT(static_cast<int>(Region::kPostObserved),
            static_cast<int>(Region::kObserved));
  EXPECT_LT(static_cast<int>(Region::kPreReNBA),
            static_cast<int>(Region::kReNBA));
  EXPECT_GT(static_cast<int>(Region::kPostReNBA),
            static_cast<int>(Region::kReNBA));
  EXPECT_LT(static_cast<int>(Region::kPrePostponed),
            static_cast<int>(Region::kPostponed));
}

TEST(SchedulerOverviewSim, PLIPreActiveBeforeSimulationActive) {
  VerifyTwoRegionOrder({Region::kPreActive, "pre_active"},
                       {Region::kActive, "active"});
}

TEST(SchedulerOverviewSim, PLIPrePostponedBeforePostponed) {
  VerifyTwoRegionOrder({Region::kPrePostponed, "pre_postponed"},
                       {Region::kPostponed, "postponed"});
}

TEST(SchedulerOverviewSim, PLIPostNBAAfterNBABeforePreObserved) {
  VerifyThreeRegionOrder({Region::kNBA, "nba"}, {Region::kPostNBA, "post_nba"},
                         {Region::kPreObserved, "pre_observed"});
}

TEST(SchedulerOverviewSim, FullPipelineIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, d;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    #10 a = 8'd10;\n"
      "  end\n"
      "  assign b = a + 8'd1;\n"
      "  always_comb c = b * 8'd2;\n"
      "  initial begin\n"
      "    d <= 8'd0;\n"
      "    #10 d <= 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 11u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 22u);
  EXPECT_EQ(f.ctx.FindVariable("d")->value.ToUint64(), 99u);
}

}  // namespace
