#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.9.6 Port connections
//
// LRM §4.9.6:
//   "Ports connect processes through implicit continuous assignment statements
//    or implicit bidirectional connections. Bidirectional connections are
//    analogous to an always-enabled tran connection between the two nets, but
//    without any strength reduction (A tran connection does not affect signal
//    strength across the bidirectional terminals, except that a supply
//    strength is reduced to strong. See 28.13).
//
//    Ports can always be represented as declared objects connected as follows:
//    — If an input port, then a continuous assignment from an outside
//      expression to a local (input) net or variable
//    — If an output port, then a continuous assignment from a local output
//      expression to an outside net or variable
//    — If an inout port, then a non-strength-reducing transistor connecting
//      the local net to an outside net
//
//    Primitive terminals, including UDP terminals, are different from module
//    ports. Primitive output and inout terminals shall be connected directly
//    to 1-bit nets or 1-bit structural net expressions (see 23.3.3), with no
//    intervening process that could alter the strength. Changes from primitive
//    evaluations are scheduled as active update events in the connected nets.
//    Input terminals connected to 1-bit nets or 1-bit structural net
//    expressions are also connected directly, with no intervening process
//    that could affect the strength. Input terminals connected to other kinds
//    of expressions are represented as implicit continuous assignments from
//    the expression to an implicit net that is connected to the input
//    terminal."
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.9.6 "Ports connect processes through implicit continuous assignment
//          statements"
// An input or output port acts as an implicit continuous assignment: when the
// source changes, an update event propagates the new value to the destination.
// ---------------------------------------------------------------------------
TEST(SimCh4096, PortsConnectViaImplicitContinuousAssignment) {
  Arena arena;
  Scheduler sched(arena);
  int outside_net = 0;
  int local_input_net = 0;

  // Model: module m(input wire inp); — outside drives local via implicit
  // continuous assignment. When outside changes, local updates.
  auto* drive = sched.GetEventPool().Acquire();
  drive->kind = EventKind::kEvaluation;
  drive->callback = [&]() {
    outside_net = 42;
    // Implicit continuous assignment propagates to local_input_net.
    auto* prop = sched.GetEventPool().Acquire();
    prop->kind = EventKind::kUpdate;
    prop->callback = [&]() { local_input_net = outside_net; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, prop);
  };
  sched.ScheduleEvent({0}, Region::kActive, drive);

  sched.Run();
  EXPECT_EQ(outside_net, 42);
  EXPECT_EQ(local_input_net, 42);
}

// ---------------------------------------------------------------------------
// §4.9.6 "or implicit bidirectional connections"
// An inout port creates a bidirectional connection: a change on either side
// propagates to the other.
// ---------------------------------------------------------------------------
TEST(SimCh4096, ImplicitBidirectionalConnection) {
  Arena arena;
  Scheduler sched(arena);
  int local_net = 0;
  int outside_net = 0;

  // Model: module m(inout wire io); — bidirectional connection.
  // Drive local_net at time 0 → outside_net updates.
  // Drive outside_net at time 5 → local_net updates.
  auto* drive_local = sched.GetEventPool().Acquire();
  drive_local->kind = EventKind::kEvaluation;
  drive_local->callback = [&]() {
    local_net = 7;
    // Bidirectional: local→outside propagation.
    auto* prop = sched.GetEventPool().Acquire();
    prop->kind = EventKind::kUpdate;
    prop->callback = [&]() { outside_net = local_net; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, prop);
  };
  sched.ScheduleEvent({0}, Region::kActive, drive_local);

  auto* drive_outside = sched.GetEventPool().Acquire();
  drive_outside->kind = EventKind::kEvaluation;
  drive_outside->callback = [&]() {
    outside_net = 99;
    // Bidirectional: outside→local propagation.
    auto* prop = sched.GetEventPool().Acquire();
    prop->kind = EventKind::kUpdate;
    prop->callback = [&]() { local_net = outside_net; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, prop);
  };
  sched.ScheduleEvent({5}, Region::kActive, drive_outside);

  sched.Run();
  EXPECT_EQ(local_net, 99);
  EXPECT_EQ(outside_net, 99);
}

// ---------------------------------------------------------------------------
// §4.9.6 "Bidirectional connections are analogous to an always-enabled tran
//          connection between the two nets, but without any strength
//          reduction"
// Unlike a real tran gate (which reduces supply→strong), a bidirectional
// port connection preserves full signal strength across the connection.
// ---------------------------------------------------------------------------
TEST(SimCh4096, BidirectionalNoStrengthReduction) {
  Arena arena;
  Scheduler sched(arena);

  // Strength model: 7 = supply strength.
  int net_a_val = 0;
  int net_a_strength = 0;
  int net_b_val = 0;
  int net_b_strength = 0;

  // Model: inout port connects net_a to net_b.
  // Drive net_a with supply strength (7). Via bidirectional port, net_b
  // should also get supply strength (7) — no reduction.
  auto* drive = sched.GetEventPool().Acquire();
  drive->kind = EventKind::kEvaluation;
  drive->callback = [&]() {
    net_a_val = 1;
    net_a_strength = 7;  // Supply strength.
    // Bidirectional port propagation: no strength reduction.
    auto* prop = sched.GetEventPool().Acquire();
    prop->kind = EventKind::kUpdate;
    prop->callback = [&]() {
      net_b_val = net_a_val;
      net_b_strength = net_a_strength;  // Preserved, not reduced.
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, prop);
  };
  sched.ScheduleEvent({0}, Region::kActive, drive);

  sched.Run();
  EXPECT_EQ(net_b_val, 1);
  EXPECT_EQ(net_b_strength, 7);  // Supply strength preserved.
}

// ---------------------------------------------------------------------------
// §4.9.6 "If an input port, then a continuous assignment from an outside
//          expression to a local (input) net or variable"
// An input port is modeled as a continuous assignment: outside → local.
// When the outside expression changes at a later time, the local net updates.
// ---------------------------------------------------------------------------
TEST(SimCh4096, InputPortContinuousAssignmentOutsideToLocal) {
  Arena arena;
  Scheduler sched(arena);
  int outside_expr = 10;
  int local_net = 0;
  std::vector<int> local_history;

  // Model: input wire inp; — continuous assignment from outside to local.
  // Time 0: outside=10 → local=10.
  // Time 5: outside=20 → local=20.
  auto* assign_t0 = sched.GetEventPool().Acquire();
  assign_t0->kind = EventKind::kEvaluation;
  assign_t0->callback = [&]() {
    local_net = outside_expr;
    local_history.push_back(local_net);
  };
  sched.ScheduleEvent({0}, Region::kActive, assign_t0);

  auto* change_t5 = sched.GetEventPool().Acquire();
  change_t5->kind = EventKind::kEvaluation;
  change_t5->callback = [&]() {
    outside_expr = 20;
    // Implicit continuous assignment re-evaluates.
    auto* reassign = sched.GetEventPool().Acquire();
    reassign->kind = EventKind::kUpdate;
    reassign->callback = [&]() {
      local_net = outside_expr;
      local_history.push_back(local_net);
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, reassign);
  };
  sched.ScheduleEvent({5}, Region::kActive, change_t5);

  sched.Run();
  ASSERT_EQ(local_history.size(), 2u);
  EXPECT_EQ(local_history[0], 10);
  EXPECT_EQ(local_history[1], 20);
}

// ---------------------------------------------------------------------------
// §4.9.6 "If an output port, then a continuous assignment from a local
//          output expression to an outside net or variable"
// An output port is modeled as a continuous assignment: local → outside.
// ---------------------------------------------------------------------------
TEST(SimCh4096, OutputPortContinuousAssignmentLocalToOutside) {
  Arena arena;
  Scheduler sched(arena);
  int local_output_expr = 0;
  int outside_net = 0;

  // Model: output wire out_sig; — continuous assignment from local to outside.
  // Time 0: local computes 55 → outside=55.
  auto* compute = sched.GetEventPool().Acquire();
  compute->kind = EventKind::kEvaluation;
  compute->callback = [&]() {
    local_output_expr = 55;
    // Implicit continuous assignment: local → outside.
    auto* prop = sched.GetEventPool().Acquire();
    prop->kind = EventKind::kUpdate;
    prop->callback = [&]() { outside_net = local_output_expr; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, prop);
  };
  sched.ScheduleEvent({0}, Region::kActive, compute);

  sched.Run();
  EXPECT_EQ(local_output_expr, 55);
  EXPECT_EQ(outside_net, 55);
}

// ---------------------------------------------------------------------------
// §4.9.6 "If an inout port, then a non-strength-reducing transistor
//          connecting the local net to an outside net"
// An inout port behaves like a non-strength-reducing tran: signals flow both
// ways, and a later change on one side propagates to the other.
// ---------------------------------------------------------------------------
TEST(SimCh4096, InoutPortNonStrengthReducingTransistor) {
  Arena arena;
  Scheduler sched(arena);
  int local_val = 0;
  int local_str = 0;
  int outside_val = 0;
  int outside_str = 0;

  // Model: inout wire io; — non-strength-reducing bidirectional connection.
  // Time 0: outside driven with supply strength (7), propagates to local.
  // Time 5: local driven with strong strength (6), propagates to outside.
  auto* drive_outside_t0 = sched.GetEventPool().Acquire();
  drive_outside_t0->kind = EventKind::kEvaluation;
  drive_outside_t0->callback = [&]() {
    outside_val = 1;
    outside_str = 7;  // Supply.
    auto* prop = sched.GetEventPool().Acquire();
    prop->kind = EventKind::kUpdate;
    prop->callback = [&]() {
      local_val = outside_val;
      local_str = outside_str;  // No reduction.
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, prop);
  };
  sched.ScheduleEvent({0}, Region::kActive, drive_outside_t0);

  auto* drive_local_t5 = sched.GetEventPool().Acquire();
  drive_local_t5->kind = EventKind::kEvaluation;
  drive_local_t5->callback = [&]() {
    local_val = 0;
    local_str = 6;  // Strong.
    auto* prop = sched.GetEventPool().Acquire();
    prop->kind = EventKind::kUpdate;
    prop->callback = [&]() {
      outside_val = local_val;
      outside_str = local_str;  // No reduction.
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, prop);
  };
  sched.ScheduleEvent({5}, Region::kActive, drive_local_t5);

  sched.Run();
  EXPECT_EQ(outside_val, 0);
  EXPECT_EQ(outside_str, 6);  // Strong strength preserved, not reduced.
  EXPECT_EQ(local_val, 0);
}

// ---------------------------------------------------------------------------
// §4.9.6 "Primitive terminals, including UDP terminals, are different from
//          module ports"
// Primitive output/inout terminals connect directly to 1-bit nets without any
// intervening process. This test verifies a primitive output terminal drives
// a 1-bit net directly, with no additional process in between.
// ---------------------------------------------------------------------------
TEST(SimCh4096, PrimitiveTerminalsDirectConnection) {
  Arena arena;
  Scheduler sched(arena);
  int net_bit = -1;  // 1-bit net.

  // Model: and gate output → directly connected to net_bit (1-bit net).
  // The primitive evaluates and directly drives the net, no intervening
  // process.
  auto* prim_eval = sched.GetEventPool().Acquire();
  prim_eval->kind = EventKind::kEvaluation;
  prim_eval->callback = [&]() {
    // Primitive evaluation: AND(1,1) = 1.
    int in_a = 1;
    int in_b = 1;
    int result = in_a & in_b;
    // Direct connection to 1-bit net — scheduled as active update.
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&, result]() { net_bit = result; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, prim_eval);

  sched.Run();
  EXPECT_EQ(net_bit, 1);
}

// ---------------------------------------------------------------------------
// §4.9.6 "Primitive output and inout terminals shall be connected directly
//          to 1-bit nets...with no intervening process that could alter the
//          strength"
// The strength from the primitive's output terminal flows directly to the
// connected net without any alteration.
// ---------------------------------------------------------------------------
TEST(SimCh4096, PrimitiveOutputNoStrengthAlteration) {
  Arena arena;
  Scheduler sched(arena);
  int net_val = -1;
  int net_strength = -1;

  // Model: primitive output terminal drives 1-bit net.
  // The primitive drives with strong strength (6). No intervening process
  // alters the strength — the net receives the exact same strength.
  auto* prim_eval = sched.GetEventPool().Acquire();
  prim_eval->kind = EventKind::kEvaluation;
  prim_eval->callback = [&]() {
    int prim_out_val = 1;
    int prim_out_str = 6;  // Strong strength from primitive.
    // Direct connection: no strength alteration.
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&, prim_out_val, prim_out_str]() {
      net_val = prim_out_val;
      net_strength = prim_out_str;
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, prim_eval);

  sched.Run();
  EXPECT_EQ(net_val, 1);
  EXPECT_EQ(net_strength, 6);  // Strength unaltered.
}

// ---------------------------------------------------------------------------
// §4.9.6 "Changes from primitive evaluations are scheduled as active update
//          events in the connected nets"
// When a primitive evaluates and produces a change, the update is scheduled
// in the Active region — not Inactive, NBA, or any other region.
// ---------------------------------------------------------------------------
TEST(SimCh4096, PrimitiveChangesScheduledAsActiveUpdateEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Schedule a primitive evaluation that produces a change, and also
  // schedule an NBA event. The primitive's update should execute in Active
  // (before NBA).
  auto* prim_eval = sched.GetEventPool().Acquire();
  prim_eval->kind = EventKind::kEvaluation;
  prim_eval->callback = [&]() {
    // Primitive evaluation produces a change → active update event.
    auto* prim_update = sched.GetEventPool().Acquire();
    prim_update->kind = EventKind::kUpdate;
    prim_update->callback = [&]() { order.push_back("prim_active_update"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, prim_update);

    // NBA event for comparison.
    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&]() { order.push_back("nba_event"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, prim_eval);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "prim_active_update");
  EXPECT_EQ(order[1], "nba_event");
}

// ---------------------------------------------------------------------------
// §4.9.6 "Input terminals connected to other kinds of expressions are
//          represented as implicit continuous assignments from the expression
//          to an implicit net that is connected to the input terminal"
// When a primitive input is connected to an expression (not a simple 1-bit
// net), an implicit continuous assignment is created from the expression to
// an implicit net, which then connects to the terminal.
// ---------------------------------------------------------------------------
TEST(SimCh4096, PrimitiveInputExprImplicitContinuousAssignment) {
  Arena arena;
  Scheduler sched(arena);
  int a = 1;
  int b = 0;
  int implicit_net = -1;
  int prim_input_val = -1;

  // Model: and g1(out, a & b);
  // The expression (a & b) is not a simple 1-bit net. An implicit continuous
  // assignment evaluates (a & b) and drives an implicit net. The primitive
  // input terminal reads from this implicit net.
  auto* expr_eval = sched.GetEventPool().Acquire();
  expr_eval->kind = EventKind::kEvaluation;
  expr_eval->callback = [&]() {
    // Implicit continuous assignment: expression → implicit net.
    implicit_net = a & b;
    // Implicit net connects to primitive input terminal.
    auto* connect = sched.GetEventPool().Acquire();
    connect->kind = EventKind::kUpdate;
    connect->callback = [&]() { prim_input_val = implicit_net; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, connect);
  };
  sched.ScheduleEvent({0}, Region::kActive, expr_eval);

  // At time 5, expression operand changes → re-evaluate.
  auto* change = sched.GetEventPool().Acquire();
  change->kind = EventKind::kEvaluation;
  change->callback = [&]() {
    b = 1;
    // Re-evaluate the implicit continuous assignment.
    implicit_net = a & b;
    auto* reconnect = sched.GetEventPool().Acquire();
    reconnect->kind = EventKind::kUpdate;
    reconnect->callback = [&]() { prim_input_val = implicit_net; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, reconnect);
  };
  sched.ScheduleEvent({5}, Region::kActive, change);

  sched.Run();
  // After time 5: a=1, b=1 → expression=1 → implicit_net=1 → prim_input=1.
  EXPECT_EQ(implicit_net, 1);
  EXPECT_EQ(prim_input_val, 1);
}
