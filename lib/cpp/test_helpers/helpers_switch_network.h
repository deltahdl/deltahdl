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

using SwitchKind = ::delta::BidirSwitchKind;

struct SwitchInst {
  Net* terminal_a = nullptr;
  Net* terminal_b = nullptr;
  SwitchKind kind = SwitchKind::kTran;
  Logic4Word control{0, 0};
  bool user_defined_nets = false;
  PassSwitchDelaySpec delay{};
};

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
  z.words[0].aval = 0;
  z.words[0].bval = 1;
  net.drivers.push_back(z);
  return net;
}

static constexpr uint8_t kVal0 = 0;
static constexpr uint8_t kVal1 = 1;
static constexpr uint8_t kValX = 2;
static constexpr uint8_t kValZ = 3;

inline uint8_t ValOf(const Variable& v) {
  uint8_t a = v.value.words[0].aval & 1;
  uint8_t b = v.value.words[0].bval & 1;
  if (b == 0) return a;
  return a ? kValX : kValZ;
}

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

inline NetPair MakeStrengthDrivenNetPair(Strength source) {
  NetPair np = MakeNetPair(1);
  np.a.resolved_strength.s1_hi = source;
  np.a.resolved_strength.s1_lo = source;
  return np;
}
