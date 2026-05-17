#include <gtest/gtest.h>

#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"
#include "simulator/vpi.h"

using namespace delta;

TEST(EventSimulationSim, DiscreteEventModelTimeAdvancesOnlyOnScheduledEvents) {
  Arena arena;
  Scheduler sched(arena);

  EXPECT_EQ(sched.CurrentTime().ticks, 0u);
  sched.Run();
  EXPECT_EQ(sched.CurrentTime().ticks, 0u);

  uint64_t observed_time = UINT64_MAX;
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { observed_time = sched.CurrentTime().ticks; };
  sched.ScheduleEvent({42}, Region::kActive, ev);

  sched.Run();
  EXPECT_EQ(observed_time, 42u);
  EXPECT_EQ(sched.CurrentTime().ticks, 42u);
}

TEST(EventSimulationSim, ProcessKindCoversLrmEnumeratedExamples) {
  EXPECT_NE(static_cast<int>(ProcessKind::kInitial),
            static_cast<int>(ProcessKind::kAlways));
  EXPECT_NE(static_cast<int>(ProcessKind::kAlways),
            static_cast<int>(ProcessKind::kAlwaysComb));
  EXPECT_NE(static_cast<int>(ProcessKind::kAlwaysComb),
            static_cast<int>(ProcessKind::kAlwaysLatch));
  EXPECT_NE(static_cast<int>(ProcessKind::kAlwaysLatch),
            static_cast<int>(ProcessKind::kAlwaysFF));
  EXPECT_NE(static_cast<int>(ProcessKind::kInitial),
            static_cast<int>(ProcessKind::kContAssign));
}

TEST(EventSimulationSim, InitialProcedureIsAnEvaluatedProcess) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd42;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 42u);
}

TEST(EventSimulationSim, NbaAssignmentSchedulesAnUpdateEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst;\n"
      "  initial dst <= 8'd9;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  EXPECT_EQ(f.scheduler.UpdateEventScheduledCount(), 0u);
  f.scheduler.Run();
  EXPECT_GE(f.scheduler.UpdateEventScheduledCount(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 9u);
}

TEST(EventSimulationSim, NetChargeDecaySchedulesAnUpdateEvent) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0xAB);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 50;
  Logic4Vec all_z = MakeLogic4Vec(arena, 8);
  for (uint32_t w = 0; w < all_z.nwords; ++w) {
    all_z.words[w].aval = ~uint64_t{0};
    all_z.words[w].bval = ~uint64_t{0};
  }
  net.drivers.push_back(all_z);
  EXPECT_EQ(sched.UpdateEventScheduledCount(), 0u);
  net.Resolve(arena, &sched);
  EXPECT_GE(sched.UpdateEventScheduledCount(), 1u);
}

TEST(EventSimulationSim, NoStateChangeMeansNoUpdateEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.scheduler.UpdateEventScheduledCount(), 0u);
}

TEST(EventSimulationSim, AllSensitiveProcessesEvaluateOnUpdateEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, a, b;\n"
      "  initial src = 8'd5;\n"
      "  always_comb a = src + 8'd1;\n"
      "  always_comb b = src + 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 7u);
}

TEST(EventSimulationSim, ProcessEvaluationSchedulesAnEvaluationEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  EXPECT_GE(f.scheduler.EvaluationEventScheduledCount(), 1u);
}

TEST(EventSimulationSim, UpdateAndEvaluationEventsAreDistinctKinds) {
  Arena arena;
  Scheduler sched(arena);

  auto* update = sched.GetEventPool().Acquire();
  update->kind = EventKind::kUpdate;
  update->callback = []() {};
  sched.ScheduleEvent({0}, Region::kNBA, update);

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = []() {};
  sched.ScheduleEvent({0}, Region::kActive, eval);

  EXPECT_EQ(sched.UpdateEventScheduledCount(), 1u);
  EXPECT_EQ(sched.EvaluationEventScheduledCount(), 1u);
}

TEST(EventSimulationSim, PliCallbacksAreScheduledAsRegionalEvaluationEvents) {
  EXPECT_TRUE(IsOneShotPliCallback(kCbAfterDelay));
  EXPECT_NE(RegionForPliCallback(kCbAfterDelay), Region::kCOUNT);
  EXPECT_NE(RegionForPliCallback(kCbReadOnlySynch), Region::kCOUNT);
  EXPECT_NE(RegionForPliCallback(kCbAtEndOfSimTime), Region::kCOUNT);
}

TEST(EventSimulationSim, FreshlyAcquiredEventDefaultsToEvaluationKind) {
  Arena arena;
  EventPool pool(arena);
  auto* ev = pool.Acquire();
  EXPECT_EQ(ev->kind, EventKind::kEvaluation);
  ev->kind = EventKind::kUpdate;
  pool.Release(ev);
  auto* recycled = pool.Acquire();
  EXPECT_EQ(recycled->kind, EventKind::kEvaluation);
}

TEST(EventSimulationSim, SchedulerMaintainsSimulationTime) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> observed_times;

  for (uint64_t t : {0, 5, 17}) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&observed_times, &sched]() {
      observed_times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kActive, ev);
  }
  sched.Run();
  ASSERT_EQ(observed_times.size(), 3u);
  EXPECT_EQ(observed_times[0], 0u);
  EXPECT_EQ(observed_times[1], 5u);
  EXPECT_EQ(observed_times[2], 17u);
}

TEST(EventSimulationSim, SingleTimeSlotIsDividedIntoOrderedRegions) {
  EXPECT_GT(kRegionCount, 1u);

  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { order.push_back("nba"); };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { order.push_back("active"); };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "nba");
}
