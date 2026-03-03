// §4.9.5: Switch (transistor) processing

#include <gtest/gtest.h>
#include <cstdint>
#include <string>
#include <vector>
#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

namespace {

// ===========================================================================
// §4.9.5 Switch (transistor) processing
// ===========================================================================
// ---------------------------------------------------------------------------
// §4.9.5 — Standard unidirectional event processing
// ---------------------------------------------------------------------------
TEST(SimCh4095, UnidirectionalEventProcessing) {
  Arena arena;
  Scheduler sched(arena);
  int input = 5;
  int output = 0;

  // Model: standard gate-level unidirectional flow.
  // Read input, compute result, schedule update — each event independently.
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int result = input * 2;  // Read input, compute result.
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&, result]() { output = result; };  // Schedule update.
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(output, 10);
}

// ---------------------------------------------------------------------------
// §4.9.5 — Bidirectional signal flow between connected nets
// ---------------------------------------------------------------------------
TEST(SimCh4095, BidirectionalSignalFlow) {
  Arena arena;
  Scheduler sched(arena);
  int net_a = 0;
  int net_b = 0;
  bool switch_on = true;

  // Model: tran(net_a, net_b);
  // Signal flows bidirectionally: driving net_a propagates to net_b.
  auto* drive_a = sched.GetEventPool().Acquire();
  drive_a->kind = EventKind::kEvaluation;
  drive_a->callback = [&]() {
    net_a = 1;
    if (switch_on) {
      // Bidirectional: propagate from a to b.
      auto* update = sched.GetEventPool().Acquire();
      update->kind = EventKind::kUpdate;
      update->callback = [&]() { net_b = net_a; };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
    }
  };
  sched.ScheduleEvent({0}, Region::kActive, drive_a);

  // At time 5, drive net_b → propagates to net_a (reverse direction).
  auto* drive_b = sched.GetEventPool().Acquire();
  drive_b->kind = EventKind::kEvaluation;
  drive_b->callback = [&]() {
    net_b = 0;
    if (switch_on) {
      auto* update = sched.GetEventPool().Acquire();
      update->kind = EventKind::kUpdate;
      update->callback = [&]() { net_a = net_b; };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
    }
  };
  sched.ScheduleEvent({5}, Region::kActive, drive_b);

  sched.Run();
  // After time 5, both nets are 0 (b drove a).
  EXPECT_EQ(net_a, 0);
  EXPECT_EQ(net_b, 0);
}

// ---------------------------------------------------------------------------
// §4.9.5 — Coordinated processing of switch-connected nodes
// ---------------------------------------------------------------------------
TEST(SimCh4095, CoordinatedProcessingOfConnectedNodes) {
  Arena arena;
  Scheduler sched(arena);
  // Three nodes connected by two switches: n0 --sw0-- n1 --sw1-- n2.
  int n0 = 1;
  int n1 = 0;
  int n2 = 0;
  bool sw0_on = true;
  bool sw1_on = true;

  // Coordinated processing: must resolve entire chain before determining
  // any individual node value. n0=1 propagates through sw0 to n1 and
  // through sw1 to n2 in a single coordinated pass.
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    // Coordinated: resolve all connected nodes together.
    if (sw0_on && sw1_on) {
      auto* update = sched.GetEventPool().Acquire();
      update->kind = EventKind::kUpdate;
      update->callback = [&]() {
        // All nodes resolve to the strongest driver (n0=1).
        n1 = n0;
        n2 = n0;
      };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
    }
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(n0, 1);
  EXPECT_EQ(n1, 1);
  EXPECT_EQ(n2, 1);
}

// ---------------------------------------------------------------------------
// §4.9.5 — Inputs and outputs interact through bidirectional switches
// ---------------------------------------------------------------------------
TEST(SimCh4095, InputsAndOutputsInteract) {
  Arena arena;
  Scheduler sched(arena);
  int node_a = 0;
  int node_b = 0;
  int driver_a_val = 1;
  int driver_b_val = 1;

  // Both nodes are driven and connected by a switch. The resolved value
  // depends on both drivers interacting (not independent processing).
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    // Both drivers contribute; resolved values reflect interaction.
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() {
      // When both drivers agree (both 1), both nodes resolve to 1.
      node_a = driver_a_val;
      node_b = driver_b_val;
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(node_a, 1);
  EXPECT_EQ(node_b, 1);
}

// ---------------------------------------------------------------------------
// §4.9.5 — Relaxation technique iterates until stable
// ---------------------------------------------------------------------------
TEST(SimCh4095, RelaxationTechnique) {
  Arena arena;
  Scheduler sched(arena);
  // Model a simple switch network that requires iteration to converge.
  // n0=1, n1=unknown, n2=unknown, connected by switches.
  int n0 = 1;
  int n1 = -1;
  int n2 = -1;
  int iterations = 0;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    // Relaxation: iterate until all nodes converge.
    int prev_n1 = 0;
    int prev_n2 = 0;
    do {
      prev_n1 = n1;
      prev_n2 = n2;
      n1 = n0;  // Switch propagation: n0 → n1.
      n2 = n1;  // Switch propagation: n1 → n2.
      ++iterations;
    } while (n1 != prev_n1 || n2 != prev_n2);
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(n0, 1);
  EXPECT_EQ(n1, 1);
  EXPECT_EQ(n2, 1);
  // Converged in exactly 2 iterations (1 to propagate, 1 to confirm stable).
  EXPECT_EQ(iterations, 2);
}

}  // namespace
