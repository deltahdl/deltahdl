#pragma once

#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

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

inline bool SwitchConducts(SwitchKind kind, Logic4Word control) {
  uint8_t c_aval = control.aval & 1;
  uint8_t c_bval = control.bval & 1;
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

inline bool SwitchControlIsUnknown(SwitchKind kind, Logic4Word control) {
  if (kind == SwitchKind::kTran || kind == SwitchKind::kRtran) return false;
  uint8_t c_bval = control.bval & 1;
  return c_bval != 0;
}

inline bool IsZ(const Logic4Word& w) {
  return (w.aval & 1) != 0 && (w.bval & 1) != 0;
}

inline Logic4Vec GetDriverValue(const Net& net, const Variable& var) {
  return !net.drivers.empty() ? net.drivers[0] : var.value;
}

inline bool IsActiveDriver(const Net& net, const Logic4Vec& drv) {
  return !net.drivers.empty() && !IsZ(drv.words[0]);
}

inline void ResolveOneTerminal(Variable& terminal_var,
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

inline void ResolveUnknownControlBuiltinSwitch(const SwitchInst& sw) {
  auto& va = *sw.terminal_a->resolved;
  auto& vb = *sw.terminal_b->resolved;
  auto a_driven = GetDriverValue(*sw.terminal_a, va);
  auto b_driven = GetDriverValue(*sw.terminal_b, vb);
  bool a_is_driven = IsActiveDriver(*sw.terminal_a, a_driven);
  bool b_is_driven = IsActiveDriver(*sw.terminal_b, b_driven);
  ResolveOneTerminal(vb, b_driven, b_is_driven, a_driven, a_is_driven);
  ResolveOneTerminal(va, a_driven, a_is_driven, b_driven, b_is_driven);
}

inline void PropagateConductingSwitch(const SwitchInst& sw) {
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

inline bool HasValidTerminals(const SwitchInst& sw) {
  return sw.terminal_a && sw.terminal_b && sw.terminal_a->resolved &&
         sw.terminal_b->resolved;
}

inline void InitializeTerminals(std::vector<SwitchInst>& switches) {
  for (auto& sw : switches) {
    for (auto* net : {sw.terminal_a, sw.terminal_b}) {
      if (net && net->resolved && !net->drivers.empty()) {
        net->resolved->value = net->drivers[0];
      }
    }
  }
}

inline void ResolveSwitchFirstPass(std::vector<SwitchInst>& switches) {
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

inline void ChainPropagate(std::vector<SwitchInst>& switches) {
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

inline void ResolveSwitchNetwork(std::vector<SwitchInst>& switches,
                                 Arena& /*arena*/) {
  InitializeTerminals(switches);
  ResolveSwitchFirstPass(switches);
  ChainPropagate(switches);
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
