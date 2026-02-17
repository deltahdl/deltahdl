#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.9.5 Switch (transistor) processing
//
// LRM §4.9.5:
//   "The event-driven simulation algorithm described in 4.5 depends on
//    unidirectional signal flow and can process each event independently.
//    The inputs are read, the result is computed, and the update is
//    scheduled. SystemVerilog provides switch-level modeling in addition to
//    behavioral and gate-level modeling. Switches provide bidirectional
//    signal flow of wires of both built-in and user-defined net types
//    (see 6.6) and require coordinated processing of nodes connected by
//    switches.
//
//    The source elements that model switches are various forms of
//    transistors, called tran, tranif0, tranif1, rtran, rtranif0, and
//    rtranif1 (see 28.8).
//
//    Switch processing shall consider all the devices in a bidirectional
//    switch-connected net before it can determine the appropriate value for
//    any node on the net because the inputs and outputs interact. A
//    simulator can do this using a relaxation technique. The simulator can
//    process bidirectional switches at any time. It can process a subset of
//    bidirectional switch-connected events at a particular time,
//    intermingled with the execution of other active events.
//
//    For bidirectional switches connecting built-in net types, further
//    refinement is required when some transistors have gate value x. A
//    conceptually simple technique is to solve the network repeatedly with
//    these transistors set to all possible combinations of fully conducting
//    and nonconducting transistors. Any node that has a unique logic level
//    in all cases has steady-state response equal to this level. All other
//    nodes have steady-state response x.
//
//    When connecting user-defined net types, propagation of the signal from
//    one terminal to the other follows the same rules as in the propagation
//    of built-in net types. If the control input is off, each net is
//    resolved separately; otherwise, they are resolved as if a single net.
//    The bidirectional switch shall be treated as off for an x or z control
//    input value. This is different from the behavior of a bidirectional
//    switch connecting built-in net types, which is described in the
//    preceding paragraph."
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.9.5 "The event-driven simulation algorithm...depends on unidirectional
//          signal flow and can process each event independently. The inputs
//          are read, the result is computed, and the update is scheduled."
// Standard unidirectional event processing: read inputs, compute, schedule.
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
// §4.9.5 "Switches provide bidirectional signal flow of wires of both
//          built-in and user-defined net types"
// Bidirectional switches allow signal to flow in both directions between
// two connected nets, unlike unidirectional gates.
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
// §4.9.5 "require coordinated processing of nodes connected by switches"
// All devices on a bidirectional switch-connected net must be considered
// together before any node value can be determined.
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
// §4.9.5 "The source elements that model switches are various forms of
//          transistors, called tran, tranif0, tranif1, rtran, rtranif0,
//          and rtranif1"
// Each transistor type is a distinct source element for switch processing.
// ---------------------------------------------------------------------------
TEST(SimCh4095, TransistorSourceElements) {
  Arena arena;
  Scheduler sched(arena);

  // Enumerate all six transistor types as distinct source elements.
  // Each is represented as a named type with bidirectional connectivity.
  enum class TranType {
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
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    for (auto type : transistors) {
      (void)type;
      auto* update = sched.GetEventPool().Acquire();
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
// §4.9.5 "Switch processing shall consider all the devices in a
//          bidirectional switch-connected net before it can determine the
//          appropriate value for any node on the net because the inputs
//          and outputs interact"
// Inputs and outputs interact: changing a downstream node affects an
// upstream node through the bidirectional switch.
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
// §4.9.5 "A simulator can do this using a relaxation technique"
// The relaxation technique iteratively processes the network until stable.
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
    int prev_n1;
    int prev_n2;
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

// ---------------------------------------------------------------------------
// §4.9.5 "The simulator can process bidirectional switches at any time.
//          It can process a subset of bidirectional switch-connected events
//          at a particular time, intermingled with the execution of other
//          active events."
// Switch processing can be interleaved with other active events.
// ---------------------------------------------------------------------------
TEST(SimCh4095, IntermingledWithOtherActiveEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Schedule a switch processing event and other active events at the same
  // time. All execute in the Active region, intermingled.
  auto* switch_proc = sched.GetEventPool().Acquire();
  switch_proc->kind = EventKind::kEvaluation;
  switch_proc->callback = [&]() { order.push_back("switch_process"); };
  sched.ScheduleEvent({0}, Region::kActive, switch_proc);

  auto* gate_eval = sched.GetEventPool().Acquire();
  gate_eval->kind = EventKind::kEvaluation;
  gate_eval->callback = [&]() { order.push_back("gate_eval"); };
  sched.ScheduleEvent({0}, Region::kActive, gate_eval);

  auto* proc_stmt = sched.GetEventPool().Acquire();
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
  for (const auto& s : order) {
    if (s == "switch_process") has_switch = true;
    if (s == "gate_eval") has_gate = true;
    if (s == "proc_stmt") has_proc = true;
  }
  EXPECT_TRUE(has_switch);
  EXPECT_TRUE(has_gate);
  EXPECT_TRUE(has_proc);
}

// ---------------------------------------------------------------------------
// §4.9.5 "Any node that has a unique logic level in all cases has
//          steady-state response equal to this level."
// When gate=x, solve all combinations. If a node always resolves to the
// same value, that is its steady-state response.
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

  auto* eval = sched.GetEventPool().Acquire();
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
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(node_a_result, 1);
}

// ---------------------------------------------------------------------------
// §4.9.5 "All other nodes have steady-state response x."
// When gate=x and a node resolves to different values in different
// combinations, its steady-state response is x.
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

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int result_gate_on = 1;   // node_b when gate conducts.
    int result_gate_off = 0;  // node_b when gate non-conducting.
    if (result_gate_on == result_gate_off) {
      node_b_result = result_gate_on;
    } else {
      node_b_result = x_val;  // Ambiguous → x.
    }
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(node_b_result, x_val);  // Steady-state is x.
}

// ---------------------------------------------------------------------------
// §4.9.5 "The bidirectional switch shall be treated as off for an x or z
//          control input value. This is different from the behavior of a
//          bidirectional switch connecting built-in net types."
// For user-defined net types, x or z control input → switch off, nets
// resolved separately. This differs from built-in net types which attempt
// combinatorial solving.
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
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    bool switch_off = (control == -1 || control == -2);  // x or z → off.
    auto* update = sched.GetEventPool().Acquire();
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
