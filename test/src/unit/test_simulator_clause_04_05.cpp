// §4.5: SystemVerilog simulation reference algorithm

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

// ===========================================================================
// §4.2 Execution of a hardware model and its verification environment
//
// LRM §4.2 establishes the fundamental execution model:
//   - SystemVerilog is a parallel programming language.
//   - Certain constructs execute as parallel blocks or processes.
//   - Understanding guaranteed vs. indeterminate execution order is key.
//   - Semantics are defined for simulation.
//
// These tests verify the simulation-level behaviour of the concepts
// introduced in §4.2, covering parallel process execution, sequential
// ordering within processes, and interaction between concurrent elements.
// ===========================================================================

namespace {

// ---------------------------------------------------------------------------
// 15. §4.2 Simulation-defined semantics: time slot 0 processes all initial
//     block assignments (simulation is the canonical model).
// ---------------------------------------------------------------------------
TEST(SimCh4, TimeZeroSemantics) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = a + 8'd1;\n"
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
  EXPECT_EQ(va->value.ToUint64(), 1u);
  EXPECT_EQ(vb->value.ToUint64(), 2u);
}

// ---------------------------------------------------------------------------
// 17. §4.2 Process interaction over multiple time steps: initial block
//     updates value at different times, always_comb tracks changes.
// ---------------------------------------------------------------------------
TEST(SimCh4, ProcessInteractionMultipleTimeSteps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, doubled;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    #5 a = 8'd4;\n"
      "    #5 a = 8'd8;\n"
      "  end\n"
      "  always_comb doubled = a * 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("doubled");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

// ---------------------------------------------------------------------------
// 30. §4.2 Simulation semantics are canonical: multiple process types
//     (initial, always_comb, assign) all produce deterministic results
//     defined by the simulation model.
// ---------------------------------------------------------------------------
TEST(SimCh4, CanonicalSimulationSemantics) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, d;\n"
      "  initial a = 8'd4;\n"
      "  assign b = a + 8'd10;\n"
      "  always_comb c = b - 8'd5;\n"
      "  assign d = c * 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // a=4, b=14, c=9, d=18
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 14u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 9u);
  EXPECT_EQ(f.ctx.FindVariable("d")->value.ToUint64(), 18u);
}

// ===========================================================================
// §4.5 SystemVerilog simulation reference algorithm
//
// LRM §4.5 specifies three pseudocode functions:
//
//   execute_simulation:
//     T = 0; initialize all nets/variables; schedule initialization events
//     into time zero; advance through nonempty time slots in order.
//
//   execute_time_slot:
//     Preponed -> Pre-Active -> iterative {Active set -> Reactive set ->
//     Pre-Postponed} -> Postponed
//
//   execute_region:
//     While region is nonempty, remove event, dispatch (update or eval).
//
// The iterative regions are: Active, Inactive, Pre-NBA, NBA, Post-NBA,
// Pre-Observed, Observed, Post-Observed, Reactive, Re-Inactive, Pre-Re-NBA,
// Re-NBA, Post-Re-NBA, and Pre-Postponed.
// ===========================================================================
// ---------------------------------------------------------------------------
// Simulation time starts at 0 and advances through nonempty time slots.
// ---------------------------------------------------------------------------
TEST(SimCh45, ExecuteSimulationStartsAtTimeZero) {
  Arena arena;
  Scheduler sched(arena);
  uint64_t observed_time = UINT64_MAX;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { observed_time = sched.CurrentTime().ticks; };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  EXPECT_EQ(observed_time, 0u);
}

// ---------------------------------------------------------------------------
// §4.5 execute_simulation: "while (some time slot is nonempty) { move to the
// first nonempty time slot and set T; execute_time_slot(T); }"
// Time advances through nonempty slots in order, skipping empty ones.
// ---------------------------------------------------------------------------
TEST(SimCh45, ExecuteSimulationAdvancesThroughNonemptyTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  // Schedule at times 0, 5, 10 — gaps at 1-4 and 6-9 must be skipped.
  for (uint64_t t : {0, 5, 10}) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 5u);
  EXPECT_EQ(times[2], 10u);
}

// ---------------------------------------------------------------------------
// §4.5 execute_simulation: simulation stops when all time slots are empty.
// ---------------------------------------------------------------------------
TEST(SimCh45, ExecuteSimulationStopsWhenAllTimeSlotsEmpty) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { count++; };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  EXPECT_EQ(count, 1);
  // After Run(), no more events — HasEvents() should be false.
  EXPECT_FALSE(sched.HasEvents());
}

}  // namespace
