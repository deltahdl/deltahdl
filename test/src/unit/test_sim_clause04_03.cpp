#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/process.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

// ===========================================================================
// §4.3 Event simulation
//
// LRM §4.3 defines the discrete event execution model:
//   - Processes are objects that can be evaluated, have state, and respond
//     to changes on their inputs to produce outputs.
//   - Examples: initial, always, always_comb, always_latch, always_ff
//     procedures; continuous assignments; procedural assignments.
//   - Every change in state of a net or variable is an update event.
//   - Processes sensitive to update events are evaluated (evaluation events)
//     in an arbitrary order.
//   - Simulation time models the actual time of the system being simulated.
//   - A single time slot is divided into multiple regions for ordering.
// ===========================================================================

struct SimCh43Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc43(const std::string& src, SimCh43Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static uint64_t RunAndGet43(const std::string& src, const char* var_name) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var) return 0;
  return var->value.ToUint64();
}

// ---------------------------------------------------------------------------
// §4.3 Process: initial procedure is a process that can be evaluated,
// has state, and produces output.
// ---------------------------------------------------------------------------
TEST(SimCh43, InitialProcedureIsProcess) {
  auto result = RunAndGet43(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd42;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 42u);
}

// ---------------------------------------------------------------------------
// §4.3 Process: always_comb is a process that responds to input changes.
// ---------------------------------------------------------------------------
TEST(SimCh43, AlwaysCombIsProcess) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Process: always_latch is a process for latch-based logic.
// ---------------------------------------------------------------------------
TEST(SimCh43, AlwaysLatchIsProcess) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Process: always_ff is a process for flip-flop-based logic.
// ---------------------------------------------------------------------------
TEST(SimCh43, AlwaysFFIsProcess) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Process: continuous assignment is an implicit process.
// ---------------------------------------------------------------------------
TEST(SimCh43, ContinuousAssignIsProcess) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Process: procedural assignment within a begin-end is evaluated
// sequentially within the process.
// ---------------------------------------------------------------------------
TEST(SimCh43, ProceduralAssignmentInProcess) {
  auto result = RunAndGet43(
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

// ---------------------------------------------------------------------------
// §4.3 Update event: every change in state of a variable is an update event.
// A blocking assignment changes state, creating an update event.
// ---------------------------------------------------------------------------
TEST(SimCh43, BlockingAssignCreatesUpdateEvent) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Update event: non-blocking assignment creates a deferred update event
// in the NBA region.
// ---------------------------------------------------------------------------
TEST(SimCh43, NonBlockingAssignCreatesUpdateEvent) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Update event: continuous assignment change propagates as update event.
// ---------------------------------------------------------------------------
TEST(SimCh43, ContinuousAssignUpdateEvent) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Evaluation event: process sensitive to an update event re-evaluates.
// always_comb is sensitive to all RHS variables and re-evaluates on change.
// ---------------------------------------------------------------------------
TEST(SimCh43, EvaluationEventOnInputChange) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Evaluation event: multiple processes sensitive to the same update
// event all evaluate.
// ---------------------------------------------------------------------------
TEST(SimCh43, MultipleProcessesSensitiveToSameEvent) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Evaluation event: continuous assignment and always_comb both sensitive
// to the same variable both evaluate when the source is set.
// ---------------------------------------------------------------------------
TEST(SimCh43, MixedProcessTypesSensitiveToSameVariable) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Simulation time: time starts at zero.
// ---------------------------------------------------------------------------
TEST(SimCh43, SimulationTimeStartsAtZero) {
  SimCh43Fixture f;
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

// ---------------------------------------------------------------------------
// §4.3 Simulation time: processes with no delays execute at time 0.
// ---------------------------------------------------------------------------
TEST(SimCh43, NoDelayExecutesAtTimeZero) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Simulation time: a #delay advances simulation time.
// ---------------------------------------------------------------------------
TEST(SimCh43, DelayAdvancesSimulationTime) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    #10 x = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// §4.3 Simulation time: multiple delays accumulate correctly.
// ---------------------------------------------------------------------------
TEST(SimCh43, MultipleDelaysAccumulate) {
  auto result = RunAndGet43(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    #5 x = 8'd1;\n"
      "    #5 x = 8'd2;\n"
      "    #5 x = 8'd3;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 3u);
}

// ---------------------------------------------------------------------------
// §4.3 Simulation time: events at different times execute in chronological
// order (time never goes backwards).
// ---------------------------------------------------------------------------
TEST(SimCh43, EventsExecuteInChronologicalOrder) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Time slot regions: active region events execute before NBA region.
// A blocking assignment (active) and non-blocking assignment (NBA) in the
// same process demonstrate region ordering.
// ---------------------------------------------------------------------------
TEST(SimCh43, ActiveRegionBeforeNBARegion) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Time slot regions: NBA update is visible after the active region.
// The non-blocking assignment value is applied in the NBA region and can
// be observed by processes that re-evaluate.
// ---------------------------------------------------------------------------
TEST(SimCh43, NBAUpdateVisibleAfterActiveRegion) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Processes have state: a process maintains state across time steps.
// ---------------------------------------------------------------------------
TEST(SimCh43, ProcessMaintainsStateAcrossTime) {
  auto result = RunAndGet43(
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

// ---------------------------------------------------------------------------
// §4.3 Processes respond to input changes: always_comb re-evaluates each
// time an input variable changes, tracking intermediate values.
// ---------------------------------------------------------------------------
TEST(SimCh43, ProcessRespondsToMultipleInputChanges) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Processes are concurrently scheduled: multiple process types
// (initial, always_comb, assign) all execute within the same simulation.
// ---------------------------------------------------------------------------
TEST(SimCh43, ConcurrentProcessTypes) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Update event cascading: an update event triggers evaluation events,
// which may produce further update events (chain of assign statements).
// ---------------------------------------------------------------------------
TEST(SimCh43, UpdateEventCascade) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
      "module t;\n"
      "  logic [7:0] a, b, c, d;\n"
      "  initial a = 8'd1;\n"
      "  assign b = a + 8'd1;\n"
      "  assign c = b + 8'd1;\n"
      "  assign d = c + 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("d")->value.ToUint64(), 4u);
}

// ---------------------------------------------------------------------------
// §4.3 Time slot region ordering: verify that region ordering provides
// predictable interactions (properties sample stable data).
// Blocking in Active, NBA applied later, always_comb re-evaluates.
// ---------------------------------------------------------------------------
TEST(SimCh43, RegionOrderingPredictableInteraction) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Processes produce outputs: an always_comb process computes a
// combinational function and makes it visible to other processes.
// ---------------------------------------------------------------------------
TEST(SimCh43, ProcessProducesOutputVisibleToOthers) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Discrete event model: events scheduled at different simulation times
// execute in time order. Processes at time 5 execute before time 10.
// ---------------------------------------------------------------------------
TEST(SimCh43, DiscreteEventsInTimeOrder) {
  SimCh43Fixture f;
  auto* design = ElaborateSrc43(
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

// ---------------------------------------------------------------------------
// §4.3 Scheduler low-level: EventPool acquire and release cycle.
// Events are recycled for efficiency.
// ---------------------------------------------------------------------------
TEST(SimCh43, EventPoolRecycles) {
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

// ---------------------------------------------------------------------------
// §4.3 Scheduler low-level: events scheduled at the same time and region
// execute in FIFO order.
// ---------------------------------------------------------------------------
TEST(SimCh43, SameTimeAndRegionFIFO) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  for (int i = 0; i < 3; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() { order.push_back(i); };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], 0);
  EXPECT_EQ(order[1], 1);
  EXPECT_EQ(order[2], 2);
}

// ---------------------------------------------------------------------------
// §4.3 Scheduler low-level: time ordering — earlier time executes first.
// ---------------------------------------------------------------------------
TEST(SimCh43, SchedulerTimeOrdering) {
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

// ---------------------------------------------------------------------------
// §4.3 Scheduler low-level: region ordering within a time slot.
// Active executes before Inactive, Inactive before NBA.
// ---------------------------------------------------------------------------
TEST(SimCh43, SchedulerRegionOrdering) {
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

// ---------------------------------------------------------------------------
// §4.3 Update and evaluation event kinds: both EventKind::kUpdate and
// EventKind::kEvaluation are executed by the scheduler.
// ---------------------------------------------------------------------------
TEST(SimCh43, UpdateAndEvaluationEventKinds) {
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

// ---------------------------------------------------------------------------
// §4.3 Variable watcher: update events are detected via the watcher
// mechanism on Variable. A watcher is notified when NotifyWatchers is called.
// ---------------------------------------------------------------------------
TEST(SimCh43, VariableWatcherNotifiesOnUpdate) {
  Variable var;
  bool notified = false;
  var.AddWatcher([&notified]() {
    notified = true;
    return true;
  });
  var.NotifyWatchers();
  EXPECT_TRUE(notified);
}

// ---------------------------------------------------------------------------
// §4.3 Variable watcher: a watcher returning false persists for subsequent
// notifications (reusable sensitivity).
// ---------------------------------------------------------------------------
TEST(SimCh43, WatcherPersistsIfNotConsumed) {
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

// ---------------------------------------------------------------------------
// §4.3 Variable watcher: a watcher returning true is removed after first
// notification (one-shot sensitivity).
// ---------------------------------------------------------------------------
TEST(SimCh43, WatcherRemovedIfConsumed) {
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

// ---------------------------------------------------------------------------
// §4.3 Process kinds: ProcessKind enum covers all process types listed in
// the LRM (initial, always, always_comb, always_latch, always_ff, final,
// continuous assignment).
// ---------------------------------------------------------------------------
TEST(SimCh43, ProcessKindsEnumCoverage) {
  EXPECT_EQ(static_cast<int>(ProcessKind::kInitial), 0);
  EXPECT_EQ(static_cast<int>(ProcessKind::kAlways), 1);
  EXPECT_EQ(static_cast<int>(ProcessKind::kAlwaysComb), 2);
  EXPECT_EQ(static_cast<int>(ProcessKind::kAlwaysLatch), 3);
  EXPECT_EQ(static_cast<int>(ProcessKind::kAlwaysFF), 4);
  EXPECT_EQ(static_cast<int>(ProcessKind::kFinal), 5);
  EXPECT_EQ(static_cast<int>(ProcessKind::kContAssign), 6);
}

// ---------------------------------------------------------------------------
// §4.3 Process default state: a newly created Process has default state
// (active, non-reactive, home region = Active).
// ---------------------------------------------------------------------------
TEST(SimCh43, ProcessDefaultState) {
  Process proc;
  EXPECT_EQ(proc.kind, ProcessKind::kInitial);
  EXPECT_EQ(proc.home_region, Region::kActive);
  EXPECT_TRUE(proc.active);
  EXPECT_FALSE(proc.is_reactive);
  EXPECT_EQ(proc.id, 0u);
}

// ---------------------------------------------------------------------------
// §4.3 Scheduler initial state: no events, time at zero.
// ---------------------------------------------------------------------------
TEST(SimCh43, SchedulerInitialState) {
  Arena arena;
  Scheduler sched(arena);
  EXPECT_FALSE(sched.HasEvents());
  EXPECT_EQ(sched.CurrentTime().ticks, 0u);
}

// ---------------------------------------------------------------------------
// §4.3 Time slot regions: all 17 regions from §4.4 are defined and ordered.
// ---------------------------------------------------------------------------
TEST(SimCh43, AllRegionsDefined) {
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
