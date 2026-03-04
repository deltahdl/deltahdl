// §4.5: SystemVerilog simulation reference algorithm

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_scheduler_event.h"
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

// ---------------------------------------------------------------------------
// §4.5 execute_time_slot: full region chain ordering.
// Preponed -> Pre-Active -> Active set -> Reactive set -> Postponed.
// ---------------------------------------------------------------------------
TEST(SimCh45, ExecuteTimeSlotFullRegionOrdering) { VerifyAllRegionOrder(); }

// ---------------------------------------------------------------------------
// §4.5 Active set iteration: "execute_region (Active); R = first nonempty
// region in [Active ... Post-Observed]; if (R is nonempty) move events in R
// to the Active region;"
// An Inactive callback that generates Active events: Active re-executes.
// ---------------------------------------------------------------------------
TEST(SimCh45, ActiveSetIterationReExecutesActiveAfterInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Inactive callback schedules a new Active event.
  auto* inactive = sched.GetEventPool().Acquire();
  inactive->callback = [&]() {
    order.push_back("inactive");
    auto* new_active = sched.GetEventPool().Acquire();
    new_active->callback = [&]() { order.push_back("active_from_inactive"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, new_active);
  };
  sched.ScheduleEvent({0}, Region::kInactive, inactive);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "inactive");
  EXPECT_EQ(order[1], "active_from_inactive");
}

// ---------------------------------------------------------------------------
// §4.5 Active set iteration: NBA generates Active event -> re-iterates.
// An NBA callback schedules an Active event; Active set must re-iterate.
// ---------------------------------------------------------------------------
TEST(SimCh45, ActiveSetReIteratesWhenNBAGeneratesActiveEvent) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() {
    order.push_back("nba");
    auto* new_active = sched.GetEventPool().Acquire();
    new_active->callback = [&]() { order.push_back("active_from_nba"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, new_active);
  };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "nba");
  EXPECT_EQ(order[1], "active_from_nba");
}

// ---------------------------------------------------------------------------
// §4.5 Reactive set iteration: "execute_region (Reactive); R = first nonempty
// region in [Reactive ... Post-Re-NBA]; if (R is nonempty) move events in R
// to the Reactive region;"
// Re-Inactive generates Reactive event -> Reactive re-executes.
// ---------------------------------------------------------------------------
TEST(SimCh45, ReactiveSetReIteratesWhenReInactiveGeneratesReactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* re_inactive = sched.GetEventPool().Acquire();
  re_inactive->callback = [&]() {
    order.push_back("re_inactive");
    auto* new_reactive = sched.GetEventPool().Acquire();
    new_reactive->callback = [&]() {
      order.push_back("reactive_from_re_inactive");
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kReactive, new_reactive);
  };
  sched.ScheduleEvent({0}, Region::kReInactive, re_inactive);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "re_inactive");
  EXPECT_EQ(order[1], "reactive_from_re_inactive");
}

// ---------------------------------------------------------------------------
// §4.5 "if (all regions in [Active ... Post-Re-NBA] are empty)
//        execute_region (Pre-Postponed);"
// Pre-Postponed only fires after Active and Reactive sets are fully drained.
// ---------------------------------------------------------------------------
TEST(SimCh45, PrePostponedOnlyAfterActiveAndReactiveSetsEmpty) {
  VerifyThreeRegionOrder({Region::kActive, "active"},
                         {Region::kReactive, "reactive"},
                         {Region::kPrePostponed, "pre_postponed"});
}

// ---------------------------------------------------------------------------
// §4.5 Outer loop: Reactive region schedules Active event -> active set
// re-processes before Pre-Postponed can fire.
// ---------------------------------------------------------------------------
TEST(SimCh45, ReactiveRestartsActiveSetBeforePrePostponed) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Reactive generates an Active event.
  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() {
    order.push_back("reactive");
    auto* new_active = sched.GetEventPool().Acquire();
    new_active->callback = [&]() { order.push_back("active_from_reactive"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, new_active);
  };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  // Pre-Postponed must wait until both active and reactive are fully drained.
  auto* pre_postponed = sched.GetEventPool().Acquire();
  pre_postponed->callback = [&]() { order.push_back("pre_postponed"); };
  sched.ScheduleEvent({0}, Region::kPrePostponed, pre_postponed);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "reactive");
  EXPECT_EQ(order[1], "active_from_reactive");
  EXPECT_EQ(order[2], "pre_postponed");
}

// ---------------------------------------------------------------------------
// §4.5 execute_region: "while (region is nonempty) { E = any event from
// region; remove E from the region; ... }"
// Multiple events in a single region all execute (FIFO order).
// ---------------------------------------------------------------------------
TEST(SimCh45, ExecuteRegionDrainsAllEventsInFIFOOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() { order.push_back(i); };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(order.size(), 5u);
  for (int i = 0; i < 5; ++i) {
    EXPECT_EQ(order[i], i);
  }
}

// ---------------------------------------------------------------------------
// §4.5 "The Iterative regions and their order are Active, Inactive, Pre-NBA,
// NBA, Post-NBA, Pre-Observed, Observed, Post-Observed, Reactive,
// Re-Inactive, Pre-Re-NBA, Re-NBA, Post-Re-NBA, and Pre-Postponed."
// Verify these 14 regions are contiguous and in the correct order.
// ---------------------------------------------------------------------------
TEST(SimCh45, IterativeRegionOrderMatchesAlgorithm) {
  // The 14 iterative regions per §4.5.
  constexpr Region kIterativeRegions[] = {
      Region::kActive,     Region::kInactive,     Region::kPreNBA,
      Region::kNBA,        Region::kPostNBA,      Region::kPreObserved,
      Region::kObserved,   Region::kPostObserved, Region::kReactive,
      Region::kReInactive, Region::kPreReNBA,     Region::kReNBA,
      Region::kPostReNBA,  Region::kPrePostponed,
  };
  constexpr size_t kCount = sizeof(kIterativeRegions) / sizeof(Region);
  EXPECT_EQ(kCount, 14u);

  // Each ordinal must be exactly 1 greater than the previous.
  for (size_t i = 1; i < kCount; ++i) {
    auto prev = static_cast<int>(kIterativeRegions[i - 1]);
    auto curr = static_cast<int>(kIterativeRegions[i]);
    EXPECT_EQ(curr, prev + 1) << "Region ordinal gap at index " << i;
  }
}

TEST(Scheduler, InitialState) {
  Arena arena;
  Scheduler sched(arena);
  EXPECT_FALSE(sched.HasEvents());
  EXPECT_EQ(sched.CurrentTime().ticks, 0);
}

}  // namespace
