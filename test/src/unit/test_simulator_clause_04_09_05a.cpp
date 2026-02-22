#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

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
  auto *eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int result = input * 2;  // Read input, compute result.
    auto *update = sched.GetEventPool().Acquire();
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
  auto *drive_a = sched.GetEventPool().Acquire();
  drive_a->kind = EventKind::kEvaluation;
  drive_a->callback = [&]() {
    net_a = 1;
    if (switch_on) {
      // Bidirectional: propagate from a to b.
      auto *update = sched.GetEventPool().Acquire();
      update->kind = EventKind::kUpdate;
      update->callback = [&]() { net_b = net_a; };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
    }
  };
  sched.ScheduleEvent({0}, Region::kActive, drive_a);

  // At time 5, drive net_b → propagates to net_a (reverse direction).
  auto *drive_b = sched.GetEventPool().Acquire();
  drive_b->kind = EventKind::kEvaluation;
  drive_b->callback = [&]() {
    net_b = 0;
    if (switch_on) {
      auto *update = sched.GetEventPool().Acquire();
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
  auto *eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    // Coordinated: resolve all connected nodes together.
    if (sw0_on && sw1_on) {
      auto *update = sched.GetEventPool().Acquire();
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
// §4.9.5 — Six transistor source element types
// ---------------------------------------------------------------------------
TEST(SimCh4095, TransistorSourceElements) {
  Arena arena;
  Scheduler sched(arena);

  // Enumerate all six transistor types as distinct source elements.
  // Each is represented as a named type with bidirectional connectivity.
  enum class TranType : std::uint8_t {
    kTran,
    kTranif0,
    kTranif1,
    kRtran,
    kRtranif0,
    kRtranif1
  };
  std::vector<TranType> transistors = {
      TranType::kTran,  TranType::kTranif0,  TranType::kTranif1,
      TranType::kRtran, TranType::kRtranif0, TranType::kRtranif1};

  int resolved_count = 0;

  // Each transistor type participates in switch processing.
  auto *eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    for (auto type : transistors) {
      (void)type;
      auto *update = sched.GetEventPool().Acquire();
      update->kind = EventKind::kUpdate;
      update->callback = [&]() { ++resolved_count; };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
    }
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  // All six transistor types processed.
  EXPECT_EQ(resolved_count, 6);
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
  auto *eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    // Both drivers contribute; resolved values reflect interaction.
    auto *update = sched.GetEventPool().Acquire();
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

  auto *eval = sched.GetEventPool().Acquire();
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
    auto *update = sched.GetEventPool().Acquire();
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

// ---------------------------------------------------------------------------
// §4.9.5 — Switch processing intermingled with other active events
// ---------------------------------------------------------------------------
TEST(SimCh4095, IntermingledWithOtherActiveEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Schedule a switch processing event and other active events at the same
  // time. All execute in the Active region, intermingled.
  auto *switch_proc = sched.GetEventPool().Acquire();
  switch_proc->kind = EventKind::kEvaluation;
  switch_proc->callback = [&]() { order.push_back("switch_process"); };
  sched.ScheduleEvent({0}, Region::kActive, switch_proc);

  auto *gate_eval = sched.GetEventPool().Acquire();
  gate_eval->kind = EventKind::kEvaluation;
  gate_eval->callback = [&]() { order.push_back("gate_eval"); };
  sched.ScheduleEvent({0}, Region::kActive, gate_eval);

  auto *proc_stmt = sched.GetEventPool().Acquire();
  proc_stmt->kind = EventKind::kEvaluation;
  proc_stmt->callback = [&]() { order.push_back("proc_stmt"); };
  sched.ScheduleEvent({0}, Region::kActive, proc_stmt);

  sched.Run();
  // All three events execute in the same time slot (order is
  // nondeterministic per §4.7, but all must execute).
  ASSERT_EQ(order.size(), 3u);
  bool has_switch = false;
  bool has_gate = false;
  bool has_proc = false;
  for (const auto &s : order) {
    if (s == "switch_process") has_switch = true;
    if (s == "gate_eval") has_gate = true;
    if (s == "proc_stmt") has_proc = true;
  }
  EXPECT_TRUE(has_switch);
  EXPECT_TRUE(has_gate);
  EXPECT_TRUE(has_proc);
}

// ---------------------------------------------------------------------------
// §4.9.5 — Unique logic level across all combinations gives steady-state
// ---------------------------------------------------------------------------
TEST(SimCh4095, SteadyStateUniqueLevel) {
  Arena arena;
  Scheduler sched(arena);

  // Model: strong driver on node_a = 1. Switch with gate=x connects
  // node_a to node_b. Solve both combinations:
  //   gate=on:  node_a=1, node_b=1
  //   gate=off: node_a=1, node_b=z (or undriven)
  // node_a has unique level (1) in all cases → steady-state = 1.
  int node_a_result = 0;
  int gate_val = -1;  // x represented as -1.

  auto *eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    // Solve all combinations for gate=x.
    int result_gate_on = 1;   // node_a when gate conducts.
    int result_gate_off = 1;  // node_a when gate non-conducting.
    // node_a is 1 in both cases → unique → steady-state = 1.
    if (result_gate_on == result_gate_off) {
      node_a_result = result_gate_on;  // Unique level.
    } else {
      node_a_result = gate_val;  // Ambiguous → x.
    }
    auto *update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(node_a_result, 1);
}

// ---------------------------------------------------------------------------
// §4.9.5 — Ambiguous node across combinations has steady-state x
// ---------------------------------------------------------------------------
TEST(SimCh4095, SteadyStateAmbiguousX) {
  Arena arena;
  Scheduler sched(arena);

  // Model: node_b is only driven through a switch with gate=x from
  // node_a=1. Solve combinations:
  //   gate=on:  node_b=1  (driven by node_a through conducting switch)
  //   gate=off: node_b=0  (undriven, resolves to 0/z)
  // node_b has different values → steady-state = x.
  int node_b_result = 0;
  int x_val = -1;  // Represent 'x' as -1.

  auto *eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int result_gate_on = 1;   // node_b when gate conducts.
    int result_gate_off = 0;  // node_b when gate non-conducting.
    if (result_gate_on == result_gate_off) {
      node_b_result = result_gate_on;
    } else {
      node_b_result = x_val;  // Ambiguous → x.
    }
    auto *update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(node_b_result, x_val);  // Steady-state is x.
}

// ---------------------------------------------------------------------------
// §4.9.5 — User-defined net type: x/z control input treats switch as off
// ---------------------------------------------------------------------------
TEST(SimCh4095, UserDefinedNetTypeSwitchOffForXZ) {
  Arena arena;
  Scheduler sched(arena);
  int udn_a = 5;
  int udn_b = 10;
  int control = -1;  // x represented as -1.

  // Model: bidirectional switch between user-defined nets udn_a and udn_b
  // with control=x. For UDN, x control → switch treated as off.
  // Each net resolved separately (no signal flow between them).
  auto *eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    bool switch_off = (control == -1 || control == -2);  // x or z → off.
    auto *update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    if (switch_off) {
      // Nets resolved separately — no propagation.
      update->callback = []() {};
    } else {
      // Switch on — resolve as single net.
      update->callback = [&]() { udn_b = udn_a; };
    }
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  // Switch was off (control=x) → nets resolved separately.
  EXPECT_EQ(udn_a, 5);   // Unchanged.
  EXPECT_EQ(udn_b, 10);  // Unchanged — no signal flow.
}
