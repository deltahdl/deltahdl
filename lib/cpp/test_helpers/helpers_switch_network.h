#pragma once

#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "model_switch_eval.h"
#include "simulator/net.h"
#include "simulator/switch_network.h"
#include "simulator/variable.h"

using namespace delta;

// Test fixtures around the production switch-network resolver. The algorithm
// itself lives in src/simulator/switch_network.{h,cpp}; this header only
// supplies the per-test wrappers and net builders the §4.9.5 / §28.8 unit
// tests rely on.

using SwitchKind = ::delta::BidirSwitchKind;

struct SwitchInst {
  Net* terminal_a = nullptr;
  Net* terminal_b = nullptr;
  SwitchKind kind = SwitchKind::kTran;
  Logic4Word control{0, 0};
  bool user_defined_nets = false;
  // §28.8: Delay spec applies only to the control input. Network resolution
  // ignores it because the data path through the bidirectional terminals has
  // no propagation delay; the field exists so tests can assert that property.
  PassSwitchDelaySpec delay{};
};

inline bool SwitchConducts(SwitchKind kind, Logic4Word control) {
  return ::delta::BidirSwitchConducts(kind, control);
}

inline bool SwitchControlIsUnknown(SwitchKind kind, Logic4Word control) {
  return ::delta::BidirSwitchControlIsUnknown(kind, control);
}

inline bool IsZ(const Logic4Word& w) {
  return (w.aval & 1) != 0 && (w.bval & 1) != 0;
}

inline void ResolveSwitchNetwork(std::vector<SwitchInst>& switches,
                                 Arena& arena) {
  std::vector<::delta::BidirSwitchInst> prod;
  prod.reserve(switches.size());
  for (auto& sw : switches) {
    ::delta::BidirSwitchInst p{};
    p.terminal_a = sw.terminal_a;
    p.terminal_b = sw.terminal_b;
    p.kind = sw.kind;
    p.control = sw.control;
    p.user_defined_nets = sw.user_defined_nets;
    prod.push_back(p);
  }
  ::delta::ResolveBidirSwitchNetwork(prod, arena);
}

inline Net MakeNet1(Arena& arena, Variable* var, uint64_t val) {
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, val));
  return net;
}

inline Net MakeUndrivenNet(Arena& arena, Variable* var) {
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  auto z = MakeLogic4Vec(arena, 1);
  z.words[0].aval = 1;
  z.words[0].bval = 1;
  net.drivers.push_back(z);
  return net;
}

inline uint8_t ValOf(const Variable& v) {
  uint8_t a = v.value.words[0].aval & 1;
  uint8_t b = v.value.words[0].bval & 1;
  return static_cast<uint8_t>((b << 1) | a);
}

static constexpr uint8_t kVal0 = 0;
static constexpr uint8_t kVal1 = 1;
static constexpr uint8_t kValX = 2;
static constexpr uint8_t kValZ = 3;

struct NetPair {
  Arena arena;
  Variable* va = nullptr;
  Variable* vb = nullptr;
  Net a;
  Net b;
};

inline NetPair MakeNetPair(uint64_t a_val) {
  NetPair np;
  np.va = np.arena.Create<Variable>();
  np.va->value = MakeLogic4Vec(np.arena, 1);
  np.vb = np.arena.Create<Variable>();
  np.vb->value = MakeLogic4Vec(np.arena, 1);
  np.a = MakeNet1(np.arena, np.va, a_val);
  np.b = MakeUndrivenNet(np.arena, np.vb);
  return np;
}
