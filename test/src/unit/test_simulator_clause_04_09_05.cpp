#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_switch_network.h"
#include "simulator/scheduler.h"

using namespace delta;

namespace {

TEST(SimCh4095, UnidirectionalEventProcessing) {
  Arena arena;
  Scheduler sched(arena);
  int input = 5;
  int output = 0;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int result = input * 2;
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&, result]() { output = result; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(output, 10);
}

TEST(SimCh4095, BidirectionalSignalFlow) {
  Arena arena;
  Scheduler sched(arena);
  int net_a = 0;
  int net_b = 0;
  bool switch_on = true;

  auto* drive_a = sched.GetEventPool().Acquire();
  drive_a->kind = EventKind::kEvaluation;
  drive_a->callback = [&]() {
    net_a = 1;
    if (switch_on) {
      auto* update = sched.GetEventPool().Acquire();
      update->kind = EventKind::kUpdate;
      update->callback = [&]() { net_b = net_a; };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
    }
  };
  sched.ScheduleEvent({0}, Region::kActive, drive_a);

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

  EXPECT_EQ(net_a, 0);
  EXPECT_EQ(net_b, 0);
}

TEST(SimCh4095, CoordinatedProcessingOfConnectedNodes) {
  Arena arena;
  Scheduler sched(arena);

  int n0 = 1;
  int n1 = 0;
  int n2 = 0;
  bool sw0_on = true;
  bool sw1_on = true;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    if (sw0_on && sw1_on) {
      auto* update = sched.GetEventPool().Acquire();
      update->kind = EventKind::kUpdate;
      update->callback = [&]() {
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

TEST(SimCh4095, InputsAndOutputsInteract) {
  Arena arena;
  Scheduler sched(arena);
  int node_a = 0;
  int node_b = 0;
  int driver_a_val = 1;
  int driver_b_val = 1;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() {
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

TEST(SimCh4095, RelaxationTechnique) {
  Arena arena;
  Scheduler sched(arena);

  int n0 = 1;
  int n1 = -1;
  int n2 = -1;
  int iterations = 0;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int prev_n1 = 0;
    int prev_n2 = 0;
    do {
      prev_n1 = n1;
      prev_n2 = n2;
      n1 = n0;
      n2 = n1;
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

  EXPECT_EQ(iterations, 2);
}

TEST(SimCh4095, IntermingledWithOtherActiveEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

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

TEST(SimCh4095, SteadyStateUniqueLevel) {
  Arena arena;
  Scheduler sched(arena);

  int node_a_result = 0;
  int gate_val = -1;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int result_gate_on = 1;
    int result_gate_off = 1;

    if (result_gate_on == result_gate_off) {
      node_a_result = result_gate_on;
    } else {
      node_a_result = gate_val;
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

TEST(SimCh4095, SteadyStateAmbiguousX) {
  Arena arena;
  Scheduler sched(arena);

  int node_b_result = 0;
  int x_val = -1;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int result_gate_on = 1;
    int result_gate_off = 0;
    if (result_gate_on == result_gate_off) {
      node_b_result = result_gate_on;
    } else {
      node_b_result = x_val;
    }
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(node_b_result, x_val);
}

TEST(SimCh4095, UserDefinedNetTypeSwitchOffForXZ) {
  Arena arena;
  Scheduler sched(arena);
  int udn_a = 5;
  int udn_b = 10;
  int control = -1;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    bool switch_off = (control == -1 || control == -2);
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    if (switch_off) {
      update->callback = []() {};
    } else {
      update->callback = [&]() { udn_b = udn_a; };
    }
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();

  EXPECT_EQ(udn_a, 5);
  EXPECT_EQ(udn_b, 10);
}

TEST(SwitchProcessing, NetworkResolvesAllDevicesTogether) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);
  auto* vc = arena.Create<Variable>();
  vc->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeUndrivenNet(arena, vb);
  Net c = MakeUndrivenNet(arena, vc);

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTran, {}, false});
  sw.push_back({&b, &c, SwitchKind::kTran, {}, false});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kVal1);
  EXPECT_EQ(ValOf(*vc), kVal1);
}

TEST(SwitchProcessing, BuiltinNetXControlNonUniqueProducesX) {
  auto np = MakeNetPair(1);

  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kTranif1, {0, 1}, false});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValX);
}

TEST(SwitchProcessing, BuiltinNetZControlNonUniqueProducesX) {
  auto np = MakeNetPair(0);

  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kTranif1, {1, 1}, false});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValX);
}

TEST(SwitchProcessing, UserDefinedNetXControlTreatedAsOff) {
  auto np = MakeNetPair(1);
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kTranif1, {0, 1}, true});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValZ);
}

}  // namespace
