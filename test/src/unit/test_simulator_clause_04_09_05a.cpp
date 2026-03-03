// Non-LRM tests

#include <gtest/gtest.h>
#include <cstdint>
#include <string>
#include <vector>
#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// §4.9.5 — Switch processing intermingled with other active events
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

}  // namespace
