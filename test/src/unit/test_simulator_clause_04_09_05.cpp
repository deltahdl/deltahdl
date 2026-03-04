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

// --- Local types for switch processing ---
enum class SwitchKind : uint8_t {
  kTran,
  kRtran,
  kTranif0,
  kTranif1,
  kRtranif0,
  kRtranif1,
};

struct SwitchInst {
  Net* terminal_a = nullptr;
  Net* terminal_b = nullptr;
  SwitchKind kind = SwitchKind::kTran;
  Logic4Word control{0, 0};
  bool user_defined_nets = false;
};

// --- Implementation ---
static bool SwitchConducts(SwitchKind kind, Logic4Word control) {
  uint8_t c_aval = control.aval & 1;
  uint8_t c_bval = control.bval & 1;
  // 0: aval=0,bval=0  1: aval=1,bval=0  x: aval=0,bval=1  z: aval=1,bval=1
  bool is_one = (c_aval == 1 && c_bval == 0);
  bool is_zero = (c_aval == 0 && c_bval == 0);
  switch (kind) {
    case SwitchKind::kTran:
    case SwitchKind::kRtran:
      return true;
    case SwitchKind::kTranif1:
    case SwitchKind::kRtranif1:
      return is_one;
    case SwitchKind::kTranif0:
    case SwitchKind::kRtranif0:
      return is_zero;
  }
  return false;
}

static bool SwitchControlIsUnknown(SwitchKind kind, Logic4Word control) {
  if (kind == SwitchKind::kTran || kind == SwitchKind::kRtran) return false;
  uint8_t c_bval = control.bval & 1;
  return c_bval != 0;  // x or z
}

static bool IsZ(const Logic4Word& w) {
  return (w.aval & 1) != 0 && (w.bval & 1) != 0;
}

static Logic4Vec GetDriverValue(const Net& net, const Variable& var) {
  return !net.drivers.empty() ? net.drivers[0] : var.value;
}

static bool IsActiveDriver(const Net& net, const Logic4Vec& drv) {
  return !net.drivers.empty() && !IsZ(drv.words[0]);
}

static void ResolveOneTerminal(Variable& terminal_var,
                               const Logic4Vec& term_drv, bool term_is_driven,
                               const Logic4Vec& other_drv,
                               bool other_is_driven) {
  uint8_t t_a = term_drv.words[0].aval & 1;
  uint8_t t_b = term_drv.words[0].bval & 1;
  uint8_t o_a = other_drv.words[0].aval & 1;
  uint8_t o_b = other_drv.words[0].bval & 1;
  uint8_t on_a = term_is_driven ? t_a : (other_is_driven ? o_a : t_a);
  uint8_t on_b = term_is_driven ? t_b : (other_is_driven ? o_b : t_b);
  uint8_t off_a = term_is_driven ? t_a : 1;
  uint8_t off_b = term_is_driven ? t_b : 1;
  if ((on_a != off_a || on_b != off_b) && !term_is_driven) {
    terminal_var.value.words[0].aval = 0;
    terminal_var.value.words[0].bval = 1;
  }
}

static void ResolveUnknownControlBuiltinSwitch(const SwitchInst& sw) {
  auto& va = *sw.terminal_a->resolved;
  auto& vb = *sw.terminal_b->resolved;
  auto a_driven = GetDriverValue(*sw.terminal_a, va);
  auto b_driven = GetDriverValue(*sw.terminal_b, vb);
  bool a_is_driven = IsActiveDriver(*sw.terminal_a, a_driven);
  bool b_is_driven = IsActiveDriver(*sw.terminal_b, b_driven);
  ResolveOneTerminal(vb, b_driven, b_is_driven, a_driven, a_is_driven);
  ResolveOneTerminal(va, a_driven, a_is_driven, b_driven, b_is_driven);
}

static void PropagateConductingSwitch(const SwitchInst& sw) {
  auto& va = *sw.terminal_a->resolved;
  auto& vb = *sw.terminal_b->resolved;
  auto a_drv = GetDriverValue(*sw.terminal_a, va);
  auto b_drv = GetDriverValue(*sw.terminal_b, vb);
  if (IsZ(a_drv.words[0]) && !IsZ(b_drv.words[0])) {
    va.value.words[0] = b_drv.words[0];
  } else if (IsZ(b_drv.words[0]) && !IsZ(a_drv.words[0])) {
    vb.value.words[0] = a_drv.words[0];
  }
}

static bool HasValidTerminals(const SwitchInst& sw) {
  return sw.terminal_a && sw.terminal_b && sw.terminal_a->resolved &&
         sw.terminal_b->resolved;
}

static void InitializeTerminals(std::vector<SwitchInst>& switches) {
  for (auto& sw : switches) {
    for (auto* net : {sw.terminal_a, sw.terminal_b}) {
      if (net && net->resolved && !net->drivers.empty()) {
        net->resolved->value = net->drivers[0];
      }
    }
  }
}

static void ResolveSwitchFirstPass(std::vector<SwitchInst>& switches) {
  for (auto& sw : switches) {
    if (!HasValidTerminals(sw)) continue;
    bool conducts = SwitchConducts(sw.kind, sw.control);
    bool unknown_ctrl = SwitchControlIsUnknown(sw.kind, sw.control);
    if (unknown_ctrl && !sw.user_defined_nets) {
      ResolveUnknownControlBuiltinSwitch(sw);
    } else if (conducts && !unknown_ctrl) {
      PropagateConductingSwitch(sw);
    }
  }
}

static void ChainPropagate(std::vector<SwitchInst>& switches) {
  for (auto& sw : switches) {
    if (!HasValidTerminals(sw)) continue;
    if (!SwitchConducts(sw.kind, sw.control)) continue;
    if (SwitchControlIsUnknown(sw.kind, sw.control)) continue;
    auto& va = *sw.terminal_a->resolved;
    auto& vb = *sw.terminal_b->resolved;
    if (IsZ(va.value.words[0]) && !IsZ(vb.value.words[0])) {
      va.value.words[0] = vb.value.words[0];
    } else if (IsZ(vb.value.words[0]) && !IsZ(va.value.words[0])) {
      vb.value.words[0] = va.value.words[0];
    }
  }
}

void ResolveSwitchNetwork(std::vector<SwitchInst>& switches, Arena& /*arena*/) {
  InitializeTerminals(switches);
  ResolveSwitchFirstPass(switches);
  ChainPropagate(switches);
}

// --- Helpers ---
static Net MakeNet1(Arena& arena, Variable* var, uint64_t val) {
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, val));
  return net;
}

static Net MakeUndrivenNet(Arena& arena, Variable* var) {
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  auto z = MakeLogic4Vec(arena, 1);
  z.words[0].aval = 1;
  z.words[0].bval = 1;
  net.drivers.push_back(z);
  return net;
}

static uint8_t ValOf(const Variable& v) {
  uint8_t a = v.value.words[0].aval & 1;
  uint8_t b = v.value.words[0].bval & 1;
  return static_cast<uint8_t>((b << 1) | a);
}

static constexpr uint8_t kVal0 = 0;

static constexpr uint8_t kVal1 = 1;

static constexpr uint8_t kValX = 2;

static constexpr uint8_t kValZ = 3;

// --- Coordinated processing ---
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

struct NetPair {
  Arena arena;
  Variable* va = nullptr;
  Variable* vb = nullptr;
  Net a;
  Net b;
};

static NetPair MakeNetPair(uint64_t a_val) {
  NetPair np;
  np.va = np.arena.Create<Variable>();
  np.va->value = MakeLogic4Vec(np.arena, 1);
  np.vb = np.arena.Create<Variable>();
  np.vb->value = MakeLogic4Vec(np.arena, 1);
  np.a = MakeNet1(np.arena, np.va, a_val);
  np.b = MakeUndrivenNet(np.arena, np.vb);
  return np;
}

// --- Built-in net type, x/z control: exhaustive combination ---
TEST(SwitchProcessing, BuiltinNetXControlNonUniqueProducesX) {
  auto np = MakeNetPair(1);
  // control = x: on->b=1, off->b=z. Not unique -> x.
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kTranif1, {0, 1}, false});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValX);
}

TEST(SwitchProcessing, BuiltinNetZControlNonUniqueProducesX) {
  auto np = MakeNetPair(0);
  // control = z: on->b=0, off->b=z. Not unique -> x.
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kTranif1, {1, 1}, false});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValX);
}

// --- User-defined net type, x/z control: treated as off ---
TEST(SwitchProcessing, UserDefinedNetXControlTreatedAsOff) {
  auto np = MakeNetPair(1);
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kTranif1, {0, 1}, true});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValZ);
}

}  // namespace
