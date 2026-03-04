#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(SimCh4096, PortsConnectViaImplicitContinuousAssignment) {
  Arena arena;
  Scheduler sched(arena);
  int outside_net = 0;
  int local_input_net = 0;

  auto* drive = sched.GetEventPool().Acquire();
  drive->kind = EventKind::kEvaluation;
  drive->callback = [&]() {
    outside_net = 42;

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

TEST(SimCh4096, ImplicitBidirectionalConnection) {
  Arena arena;
  Scheduler sched(arena);
  int local_net = 0;
  int outside_net = 0;

  auto* drive_local = sched.GetEventPool().Acquire();
  drive_local->kind = EventKind::kEvaluation;
  drive_local->callback = [&]() {
    local_net = 7;

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

TEST(SimCh4096, BidirectionalNoStrengthReduction) {
  Arena arena;
  Scheduler sched(arena);

  int net_a_val = 0;
  int net_a_strength = 0;
  int net_b_val = 0;
  int net_b_strength = 0;

  auto* drive = sched.GetEventPool().Acquire();
  drive->kind = EventKind::kEvaluation;
  drive->callback = [&]() {
    net_a_val = 1;
    net_a_strength = 7;

    auto* prop = sched.GetEventPool().Acquire();
    prop->kind = EventKind::kUpdate;
    prop->callback = [&]() {
      net_b_val = net_a_val;
      net_b_strength = net_a_strength;
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, prop);
  };
  sched.ScheduleEvent({0}, Region::kActive, drive);

  sched.Run();
  EXPECT_EQ(net_b_val, 1);
  EXPECT_EQ(net_b_strength, 7);
}

TEST(SimCh4096, InputPortContinuousAssignmentOutsideToLocal) {
  Arena arena;
  Scheduler sched(arena);
  int outside_expr = 10;
  int local_net = 0;
  std::vector<int> local_history;

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

TEST(SimCh4096, OutputPortContinuousAssignmentLocalToOutside) {
  Arena arena;
  Scheduler sched(arena);
  int local_output_expr = 0;
  int outside_net = 0;

  auto* compute = sched.GetEventPool().Acquire();
  compute->kind = EventKind::kEvaluation;
  compute->callback = [&]() {
    local_output_expr = 55;

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

TEST(SimCh4096, InoutPortNonStrengthReducingTransistor) {
  Arena arena;
  Scheduler sched(arena);
  int local_val = 0;
  int local_str = 0;
  int outside_val = 0;
  int outside_str = 0;

  auto* drive_outside_t0 = sched.GetEventPool().Acquire();
  drive_outside_t0->kind = EventKind::kEvaluation;
  drive_outside_t0->callback = [&]() {
    outside_val = 1;
    outside_str = 7;
    auto* prop = sched.GetEventPool().Acquire();
    prop->kind = EventKind::kUpdate;
    prop->callback = [&]() {
      local_val = outside_val;
      local_str = outside_str;
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, prop);
  };
  sched.ScheduleEvent({0}, Region::kActive, drive_outside_t0);

  auto* drive_local_t5 = sched.GetEventPool().Acquire();
  drive_local_t5->kind = EventKind::kEvaluation;
  drive_local_t5->callback = [&]() {
    local_val = 0;
    local_str = 6;
    auto* prop = sched.GetEventPool().Acquire();
    prop->kind = EventKind::kUpdate;
    prop->callback = [&]() {
      outside_val = local_val;
      outside_str = local_str;
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, prop);
  };
  sched.ScheduleEvent({5}, Region::kActive, drive_local_t5);

  sched.Run();
  EXPECT_EQ(outside_val, 0);
  EXPECT_EQ(outside_str, 6);
  EXPECT_EQ(local_val, 0);
}

TEST(SimCh4096, PrimitiveTerminalsDirectConnection) {
  Arena arena;
  Scheduler sched(arena);
  int net_bit = -1;

  auto* prim_eval = sched.GetEventPool().Acquire();
  prim_eval->kind = EventKind::kEvaluation;
  prim_eval->callback = [&]() {

    int in_a = 1;
    int in_b = 1;
    int result = in_a & in_b;

    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&, result]() { net_bit = result; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, prim_eval);

  sched.Run();
  EXPECT_EQ(net_bit, 1);
}

TEST(SimCh4096, PrimitiveOutputNoStrengthAlteration) {
  Arena arena;
  Scheduler sched(arena);
  int net_val = -1;
  int net_strength = -1;

  auto* prim_eval = sched.GetEventPool().Acquire();
  prim_eval->kind = EventKind::kEvaluation;
  prim_eval->callback = [&]() {
    int prim_out_val = 1;
    int prim_out_str = 6;

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
  EXPECT_EQ(net_strength, 6);
}

TEST(SimCh4096, PrimitiveChangesScheduledAsActiveUpdateEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* prim_eval = sched.GetEventPool().Acquire();
  prim_eval->kind = EventKind::kEvaluation;
  prim_eval->callback = [&]() {

    auto* prim_update = sched.GetEventPool().Acquire();
    prim_update->kind = EventKind::kUpdate;
    prim_update->callback = [&]() { order.push_back("prim_active_update"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, prim_update);

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

TEST(SimCh4096, PrimitiveInputExprImplicitContinuousAssignment) {
  Arena arena;
  Scheduler sched(arena);
  int a = 1;
  int b = 0;
  int implicit_net = -1;
  int prim_input_val = -1;

  auto* expr_eval = sched.GetEventPool().Acquire();
  expr_eval->kind = EventKind::kEvaluation;
  expr_eval->callback = [&]() {

    implicit_net = a & b;

    auto* connect = sched.GetEventPool().Acquire();
    connect->kind = EventKind::kUpdate;
    connect->callback = [&]() { prim_input_val = implicit_net; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, connect);
  };
  sched.ScheduleEvent({0}, Region::kActive, expr_eval);

  auto* change = sched.GetEventPool().Acquire();
  change->kind = EventKind::kEvaluation;
  change->callback = [&]() {
    b = 1;

    implicit_net = a & b;
    auto* reconnect = sched.GetEventPool().Acquire();
    reconnect->kind = EventKind::kUpdate;
    reconnect->callback = [&]() { prim_input_val = implicit_net; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, reconnect);
  };
  sched.ScheduleEvent({5}, Region::kActive, change);

  sched.Run();

  EXPECT_EQ(implicit_net, 1);
  EXPECT_EQ(prim_input_val, 1);
}
