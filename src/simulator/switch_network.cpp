#include "simulator/switch_network.h"

#include "common/arena.h"
#include "common/types.h"
#include "simulator/net.h"
#include "simulator/variable.h"

namespace delta {

namespace {

bool IsZWord(const Logic4Word& w) {
  return (w.aval & 1) != 0 && (w.bval & 1) != 0;
}

Logic4Vec PrimaryDriver(const Net& net, const Variable& var) {
  return !net.drivers.empty() ? net.drivers[0] : var.value;
}

bool TerminalIsActivelyDriven(const Net& net, const Logic4Vec& drv) {
  return !net.drivers.empty() && !IsZWord(drv.words[0]);
}

void ResolveAmbiguousTerminal(Variable& terminal_var,
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
    // The on-vs-off solutions disagree on this node, so the §4.9.5 rule
    // gives steady-state x.
    terminal_var.value.words[0].aval = 0;
    terminal_var.value.words[0].bval = 1;
  }
}

void ApplyAllCombinationsForBuiltinSwitch(const BidirSwitchInst& sw) {
  auto& va = *sw.terminal_a->resolved;
  auto& vb = *sw.terminal_b->resolved;
  auto a_driven = PrimaryDriver(*sw.terminal_a, va);
  auto b_driven = PrimaryDriver(*sw.terminal_b, vb);
  bool a_is_driven = TerminalIsActivelyDriven(*sw.terminal_a, a_driven);
  bool b_is_driven = TerminalIsActivelyDriven(*sw.terminal_b, b_driven);
  ResolveAmbiguousTerminal(vb, b_driven, b_is_driven, a_driven, a_is_driven);
  ResolveAmbiguousTerminal(va, a_driven, a_is_driven, b_driven, b_is_driven);
}

void PropagateAcrossClosedSwitch(const BidirSwitchInst& sw) {
  auto& va = *sw.terminal_a->resolved;
  auto& vb = *sw.terminal_b->resolved;
  auto a_drv = PrimaryDriver(*sw.terminal_a, va);
  auto b_drv = PrimaryDriver(*sw.terminal_b, vb);
  if (IsZWord(a_drv.words[0]) && !IsZWord(b_drv.words[0])) {
    va.value.words[0] = b_drv.words[0];
  } else if (IsZWord(b_drv.words[0]) && !IsZWord(a_drv.words[0])) {
    vb.value.words[0] = a_drv.words[0];
  }
}

bool TerminalsValid(const BidirSwitchInst& sw) {
  return sw.terminal_a && sw.terminal_b && sw.terminal_a->resolved &&
         sw.terminal_b->resolved;
}

void InitialiseTerminals(std::vector<BidirSwitchInst>& switches) {
  for (auto& sw : switches) {
    for (auto* net : {sw.terminal_a, sw.terminal_b}) {
      if (net && net->resolved && !net->drivers.empty()) {
        net->resolved->value = net->drivers[0];
      }
    }
  }
}

void FirstPass(std::vector<BidirSwitchInst>& switches) {
  for (auto& sw : switches) {
    if (!TerminalsValid(sw)) continue;
    bool conducts = BidirSwitchConducts(sw.kind, sw.control);
    bool unknown = BidirSwitchControlIsUnknown(sw.kind, sw.control);
    if (unknown && !sw.user_defined_nets) {
      ApplyAllCombinationsForBuiltinSwitch(sw);
    } else if (conducts && !unknown) {
      PropagateAcrossClosedSwitch(sw);
    }
    // user-defined nets with x/z control: switch is off, nets stay separate.
  }
}

void ChainPropagate(std::vector<BidirSwitchInst>& switches) {
  // Iterate to a fixed point so the result depends on the network topology
  // rather than the order switches happen to appear in `switches`. A single
  // sweep would miss a node whose feeder switch sits later in the vector.
  bool changed = true;
  while (changed) {
    changed = false;
    for (auto& sw : switches) {
      if (!TerminalsValid(sw)) continue;
      if (!BidirSwitchConducts(sw.kind, sw.control)) continue;
      if (BidirSwitchControlIsUnknown(sw.kind, sw.control)) continue;
      auto& va = *sw.terminal_a->resolved;
      auto& vb = *sw.terminal_b->resolved;
      if (IsZWord(va.value.words[0]) && !IsZWord(vb.value.words[0])) {
        va.value.words[0] = vb.value.words[0];
        changed = true;
      } else if (IsZWord(vb.value.words[0]) && !IsZWord(va.value.words[0])) {
        vb.value.words[0] = va.value.words[0];
        changed = true;
      }
    }
  }
}

}  // namespace

bool BidirSwitchConducts(BidirSwitchKind kind, Logic4Word control) {
  uint8_t c_aval = control.aval & 1;
  uint8_t c_bval = control.bval & 1;
  bool is_one = (c_aval == 1 && c_bval == 0);
  bool is_zero = (c_aval == 0 && c_bval == 0);
  switch (kind) {
    case BidirSwitchKind::kTran:
    case BidirSwitchKind::kRtran:
      return true;
    case BidirSwitchKind::kTranif1:
    case BidirSwitchKind::kRtranif1:
      return is_one;
    case BidirSwitchKind::kTranif0:
    case BidirSwitchKind::kRtranif0:
      return is_zero;
  }
  return false;
}

bool BidirSwitchControlIsUnknown(BidirSwitchKind kind, Logic4Word control) {
  if (kind == BidirSwitchKind::kTran || kind == BidirSwitchKind::kRtran) {
    return false;
  }
  return (control.bval & 1) != 0;
}

void ResolveBidirSwitchNetwork(std::vector<BidirSwitchInst>& switches,
                               Arena& /*arena*/) {
  InitialiseTerminals(switches);
  FirstPass(switches);
  ChainPropagate(switches);
}

}  // namespace delta
