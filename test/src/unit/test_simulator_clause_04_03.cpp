#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_scheduler_event.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/variable.h"

using namespace delta;

TEST(EventSimulationSim, InitialProcedureIsProcess) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd42;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 42u);
}

TEST(EventSimulationSim, AlwaysCombIsProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = 8'd5;\n"
      "  always_comb b = a + 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 6u);
}

TEST(EventSimulationSim, AlwaysLatchIsProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] d, q;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    d = 8'd99;\n"
      "  end\n"
      "  always_latch if (en) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("q")->value.ToUint64(), 99u);
}

TEST(EventSimulationSim, AlwaysFFIsProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] d, q;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    d = 8'd55;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("q")->value.ToUint64(), 55u);
}

TEST(EventSimulationSim, ContinuousAssignIsProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, dst;\n"
      "  assign dst = src;\n"
      "  initial src = 8'd33;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 33u);
}

TEST(EventSimulationSim, ProceduralAssignmentInProcess) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    x = x + 8'd5;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 15u);
}

TEST(EventSimulationSim, BlockingAssignCreatesUpdateEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = 8'd7;\n"
      "  always_comb b = a * 8'd3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 21u);
}

TEST(EventSimulationSim, NonBlockingAssignCreatesUpdateEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x <= 8'd88;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 88u);
}

TEST(EventSimulationSim, ContinuousAssignUpdateEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial a = 8'd4;\n"
      "  assign b = a + 8'd1;\n"
      "  assign c = b + 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 6u);
}

TEST(EventSimulationSim, EvaluationEventOnInputChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, result;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    #5 a = 8'd10;\n"
      "  end\n"
      "  always_comb result = a + 8'd100;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("result")->value.ToUint64(), 110u);
}

TEST(EventSimulationSim, MultipleProcessesSensitiveToSameEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, r1, r2;\n"
      "  initial src = 8'd5;\n"
      "  always_comb r1 = src + 8'd1;\n"
      "  always_comb r2 = src + 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("r1")->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("r2")->value.ToUint64(), 7u);
}

TEST(EventSimulationSim, MixedProcessTypesSensitiveToSameVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, via_assign, via_comb;\n"
      "  initial src = 8'd10;\n"
      "  assign via_assign = src * 8'd2;\n"
      "  always_comb via_comb = src * 8'd3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("via_assign")->value.ToUint64(), 20u);
  EXPECT_EQ(f.ctx.FindVariable("via_comb")->value.ToUint64(), 30u);
}

TEST(EventSimulationSim, SimulationTimeStartsAtZero) {
  SimFixture f;
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

TEST(EventSimulationSim, NoDelayExecutesAtTimeZero) {
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
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 1u);
}

TEST(EventSimulationSim, EventsExecuteInChronologicalOrder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    #10 a = 8'd10;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 b = 8'd5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 5u);
}

TEST(EventSimulationSim, ActiveRegionBeforeNBARegion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b <= 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 2u);
}

TEST(EventSimulationSim, NBAUpdateVisibleAfterActiveRegion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x <= 8'd50;\n"
      "  end\n"
      "  always_comb y = x + 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 50u);
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 51u);
}

TEST(EventSimulationSim, ProcessMaintainsStateAcrossTime) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd1;\n"
      "    #5 x = x + 8'd1;\n"
      "    #5 x = x + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 3u);
}

TEST(EventSimulationSim, ProcessRespondsToMultipleInputChanges) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, doubled;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    #5 a = 8'd5;\n"
      "    #5 a = 8'd10;\n"
      "  end\n"
      "  always_comb doubled = a * 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("doubled")->value.ToUint64(), 20u);
}

TEST(EventSimulationSim, ConcurrentProcessTypes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial a = 8'd2;\n"
      "  assign b = a + 8'd3;\n"
      "  always_comb c = b + 8'd4;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 9u);
}

TEST(EventSimulationSim, UpdateEventCascade) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, d;\n"
      "  initial a = 8'd1;\n"
      "  assign b = a + 8'd1;\n"
      "  assign c = b + 8'd1;\n"
      "  assign d = c + 8'd1;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 2u}, {"c", 3u}, {"d", 4u}});
}

TEST(EventSimulationSim, RegionOrderingPredictableInteraction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b <= 8'd20;\n"
      "  end\n"
      "  always_comb result = a + b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("result")->value.ToUint64(), 30u);
}

TEST(EventSimulationSim, ProcessProducesOutputVisibleToOthers) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, mid, out;\n"
      "  initial a = 8'd6;\n"
      "  always_comb mid = a * 8'd2;\n"
      "  assign out = mid + 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("mid")->value.ToUint64(), 12u);
  EXPECT_EQ(f.ctx.FindVariable("out")->value.ToUint64(), 13u);
}

TEST(EventSimulationSim, DiscreteEventsInTimeOrder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    #10 x = 8'd2;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 x = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 2u);
}

TEST(EventSimulationSim, EventPoolRecycles) {
  Arena arena;
  EventPool pool(arena);
  Event* ev = pool.Acquire();
  ASSERT_NE(ev, nullptr);
  pool.Release(ev);
  EXPECT_EQ(pool.FreeCount(), 1u);
  Event* reused = pool.Acquire();
  EXPECT_EQ(reused, ev);
  EXPECT_EQ(pool.FreeCount(), 0u);
}

TEST(EventSimulationSim, SameTimeAndRegionFIFO) { VerifyActiveRegionFIFO(); }

TEST(EventSimulationSim, SchedulerTimeOrdering) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto* ev_late = sched.GetEventPool().Acquire();
  ev_late->callback = [&order]() { order.push_back(2); };
  sched.ScheduleEvent({10}, Region::kActive, ev_late);

  auto* ev_early = sched.GetEventPool().Acquire();
  ev_early->callback = [&order]() { order.push_back(1); };
  sched.ScheduleEvent({5}, Region::kActive, ev_early);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
}

TEST(EventSimulationSim, SchedulerRegionOrdering) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* ev_nba = sched.GetEventPool().Acquire();
  ev_nba->callback = [&order]() { order.push_back("nba"); };
  sched.ScheduleEvent({0}, Region::kNBA, ev_nba);

  auto* ev_inactive = sched.GetEventPool().Acquire();
  ev_inactive->callback = [&order]() { order.push_back("inactive"); };
  sched.ScheduleEvent({0}, Region::kInactive, ev_inactive);

  auto* ev_active = sched.GetEventPool().Acquire();
  ev_active->callback = [&order]() { order.push_back("active"); };
  sched.ScheduleEvent({0}, Region::kActive, ev_active);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "inactive");
  EXPECT_EQ(order[2], "nba");
}

TEST(EventSimulationSim, UpdateAndEvaluationEventKinds) {
  Arena arena;
  Scheduler sched(arena);
  bool update_ran = false;
  bool eval_ran = false;

  auto* ev_up = sched.GetEventPool().Acquire();
  ev_up->kind = EventKind::kUpdate;
  ev_up->callback = [&update_ran]() { update_ran = true; };
  sched.ScheduleEvent({0}, Region::kActive, ev_up);

  auto* ev_ev = sched.GetEventPool().Acquire();
  ev_ev->kind = EventKind::kEvaluation;
  ev_ev->callback = [&eval_ran]() { eval_ran = true; };
  sched.ScheduleEvent({0}, Region::kActive, ev_ev);

  sched.Run();
  EXPECT_TRUE(update_ran);
  EXPECT_TRUE(eval_ran);
}

TEST(EventSimulationSim, VariableWatcherNotifiesOnUpdate) {
  Variable var;
  bool notified = false;
  var.AddWatcher([&notified]() {
    notified = true;
    return true;
  });
  var.NotifyWatchers();
  EXPECT_TRUE(notified);
}

TEST(EventSimulationSim, WatcherPersistsIfNotConsumed) {
  Variable var;
  int count = 0;
  var.AddWatcher([&count]() {
    count++;
    return false;
  });
  var.NotifyWatchers();
  var.NotifyWatchers();
  EXPECT_EQ(count, 2);
}

TEST(EventSimulationSim, WatcherRemovedIfConsumed) {
  Variable var;
  int count = 0;
  var.AddWatcher([&count]() {
    count++;
    return true;
  });
  var.NotifyWatchers();
  var.NotifyWatchers();
  EXPECT_EQ(count, 1);
}

TEST(EventSimulationSim, ProcessKindsEnumCoverage) {
  EXPECT_EQ(static_cast<int>(ProcessKind::kInitial), 0);
  EXPECT_EQ(static_cast<int>(ProcessKind::kAlways), 1);
  EXPECT_EQ(static_cast<int>(ProcessKind::kAlwaysComb), 2);
  EXPECT_EQ(static_cast<int>(ProcessKind::kAlwaysLatch), 3);
  EXPECT_EQ(static_cast<int>(ProcessKind::kAlwaysFF), 4);
  EXPECT_EQ(static_cast<int>(ProcessKind::kFinal), 5);
  EXPECT_EQ(static_cast<int>(ProcessKind::kContAssign), 6);
}

TEST(EventSimulationSim, ProcessDefaultState) {
  Process proc;
  EXPECT_EQ(proc.kind, ProcessKind::kInitial);
  EXPECT_EQ(proc.home_region, Region::kActive);
  EXPECT_TRUE(proc.active);
  EXPECT_FALSE(proc.is_reactive);
  EXPECT_EQ(proc.id, 0u);
}

TEST(EventSimulationSim, SchedulerInitialState) {
  Arena arena;
  Scheduler sched(arena);
  EXPECT_FALSE(sched.HasEvents());
  EXPECT_EQ(sched.CurrentTime().ticks, 0u);
}

TEST(EventSimulationSim, AllRegionsDefined) {
  EXPECT_EQ(static_cast<int>(Region::kPreponed), 0);
  EXPECT_EQ(static_cast<int>(Region::kPreActive), 1);
  EXPECT_EQ(static_cast<int>(Region::kActive), 2);
  EXPECT_EQ(static_cast<int>(Region::kInactive), 3);
  EXPECT_EQ(static_cast<int>(Region::kPreNBA), 4);
  EXPECT_EQ(static_cast<int>(Region::kNBA), 5);
  EXPECT_EQ(static_cast<int>(Region::kPostNBA), 6);
  EXPECT_EQ(static_cast<int>(Region::kPreObserved), 7);
  EXPECT_EQ(static_cast<int>(Region::kObserved), 8);
  EXPECT_EQ(static_cast<int>(Region::kPostObserved), 9);
  EXPECT_EQ(static_cast<int>(Region::kReactive), 10);
  EXPECT_EQ(static_cast<int>(Region::kReInactive), 11);
  EXPECT_EQ(static_cast<int>(Region::kPreReNBA), 12);
  EXPECT_EQ(static_cast<int>(Region::kReNBA), 13);
  EXPECT_EQ(static_cast<int>(Region::kPostReNBA), 14);
  EXPECT_EQ(static_cast<int>(Region::kPrePostponed), 15);
  EXPECT_EQ(static_cast<int>(Region::kPostponed), 16);
  EXPECT_EQ(kRegionCount, 17u);
}

TEST(SchedulingSemanticsSim, BehavioralAndDataflowCoexist) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  assign b = a + 8'd1;\n"
      "  initial a = 8'd5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 5u);
  EXPECT_EQ(vb->value.ToUint64(), 6u);
}

TEST(SchedulingSemanticsSim, MultipleProcessesAcrossTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    #5 a = 8'd2;\n"
      "  end\n"
      "  initial begin\n"
      "    b = 8'd10;\n"
      "    #10 b = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 2u);
  EXPECT_EQ(vb->value.ToUint64(), 20u);
}

TEST(SchedulingSemanticsSim, CascadeOfProcesses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial a = 8'd5;\n"
      "  assign b = a + 8'd1;\n"
      "  always_comb c = b * 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 12u);
}

TEST(SchedulingSemanticsSim, InterleavedTimeExecution) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    #5 a = 8'd1;\n"
      "    #10 a = 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    #10 b = 8'd2;\n"
      "    #5 b = 8'd4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 4u);
}
