#include "simulator/switch_network.h"

#include "common/arena.h"
#include "common/types.h"
#include "simulator/net.h"
#include "simulator/variable.h"

namespace delta {

namespace {

bool IsZWord(const Logic4Word& w) {
  return (w.aval & 1) == 0 && (w.bval & 1) != 0;  // z = (aval=0, bval=1)
}

Logic4Vec PrimaryDriver(const Net& net, const Variable& var) {
  return !net.drivers.empty() ? net.drivers[0] : var.value;
}

bool TerminalIsActivelyDriven(const Net& net, const Logic4Vec& drv) {
  return !net.drivers.empty() && !IsZWord(drv.words[0]);
}

// §28.13: tran, tranif0, and tranif1 are the nonresistive bidirectional pass
// switches. The r-prefixed variants are resistive and reduce strength under the
// separate rules of §28.14, so they are excluded here.
bool IsNonresistiveBidir(BidirSwitchKind kind) {
  return kind == BidirSwitchKind::kTran || kind == BidirSwitchKind::kTranif0 ||
         kind == BidirSwitchKind::kTranif1;
}

// §28.13: a nonresistive bidirectional switch does not affect the strength of a
// signal crossing between its terminals, except that a supply strength is
// reduced to a strong strength. That is exactly the reduction the nonresistive
// unidirectional switches apply (§28.13, first sentence), so the destination
// terminal receives the source strength passed through ReduceNonresistive.
//
// §28.8: there shall be no strength reduction in bidirectional switches
// connecting user-defined net types. Such a switch passes the source strength
// unchanged regardless of whether it is a resistive (r-prefixed) variant, so
// the user-defined-net case bypasses both the §28.13 and §28.14 reductions.
void PassStrengthAcross(Net& dest, const Net& src, BidirSwitchKind kind,
                        bool user_defined_nets) {
  if (user_defined_nets) {
    dest.resolved_strength = src.resolved_strength;
    return;
  }
  if (!IsNonresistiveBidir(kind)) return;
  NetStrength s = src.resolved_strength;
  s.s0_hi = ReduceNonresistive(s.s0_hi);
  s.s0_lo = ReduceNonresistive(s.s0_lo);
  s.s1_hi = ReduceNonresistive(s.s1_hi);
  s.s1_lo = ReduceNonresistive(s.s1_lo);
  dest.resolved_strength = s;
}

void ResolveAmbiguousTerminal(Variable& terminal_var, const Logic4Vec& term_drv,
                              bool term_is_driven, const Logic4Vec& other_drv,
                              bool other_is_driven) {
  uint8_t t_a = term_drv.words[0].aval & 1;
  uint8_t t_b = term_drv.words[0].bval & 1;
  uint8_t o_a = other_drv.words[0].aval & 1;
  uint8_t o_b = other_drv.words[0].bval & 1;
  uint8_t on_a = term_is_driven ? t_a : (other_is_driven ? o_a : t_a);
  uint8_t on_b = term_is_driven ? t_b : (other_is_driven ? o_b : t_b);
  // Undriven "off" state is high-impedance z = (aval=0, bval=1).
  uint8_t off_a = term_is_driven ? t_a : 0;
  uint8_t off_b = term_is_driven ? t_b : 1;
  if ((on_a != off_a || on_b != off_b) && !term_is_driven) {
    terminal_var.value.words[0].aval = 1;  // ambiguous -> x = (aval=1, bval=1)
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
    PassStrengthAcross(*sw.terminal_a, *sw.terminal_b, sw.kind,
                       sw.user_defined_nets);
  } else if (IsZWord(b_drv.words[0]) && !IsZWord(a_drv.words[0])) {
    vb.value.words[0] = a_drv.words[0];
    PassStrengthAcross(*sw.terminal_b, *sw.terminal_a, sw.kind,
                       sw.user_defined_nets);
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
  }
}

bool SwitchEligibleForChainPropagate(const BidirSwitchInst& sw) {
  if (!TerminalsValid(sw)) return false;
  if (!BidirSwitchConducts(sw.kind, sw.control)) return false;
  if (BidirSwitchControlIsUnknown(sw.kind, sw.control)) return false;
  return true;
}

bool ChainPropagateOnce(BidirSwitchInst& sw) {
  if (!SwitchEligibleForChainPropagate(sw)) return false;
  auto& va = *sw.terminal_a->resolved;
  auto& vb = *sw.terminal_b->resolved;
  if (IsZWord(va.value.words[0]) && !IsZWord(vb.value.words[0])) {
    va.value.words[0] = vb.value.words[0];
    PassStrengthAcross(*sw.terminal_a, *sw.terminal_b, sw.kind,
                       sw.user_defined_nets);
    return true;
  }
  if (IsZWord(vb.value.words[0]) && !IsZWord(va.value.words[0])) {
    vb.value.words[0] = va.value.words[0];
    PassStrengthAcross(*sw.terminal_b, *sw.terminal_a, sw.kind,
                       sw.user_defined_nets);
    return true;
  }
  return false;
}

void ChainPropagate(std::vector<BidirSwitchInst>& switches) {
  bool changed = true;
  while (changed) {
    changed = false;
    for (auto& sw : switches) {
      if (ChainPropagateOnce(sw)) changed = true;
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

uint64_t BidirSwitchTurnOnDelay(const BidirSwitchDelaySpec& spec) {
  return spec.has_turn_on ? spec.turn_on : 0;
}

uint64_t BidirSwitchTurnOffDelay(const BidirSwitchDelaySpec& spec) {
  if (spec.has_turn_off) return spec.turn_off;
  if (spec.has_turn_on) return spec.turn_on;
  return 0;
}

uint64_t BidirSwitchBuiltinControlXZDelay(const BidirSwitchDelaySpec& spec) {
  if (spec.has_turn_off)
    return spec.turn_on < spec.turn_off ? spec.turn_on : spec.turn_off;
  if (spec.has_turn_on) return spec.turn_on;
  return 0;
}

void ResolveBidirSwitchNetwork(std::vector<BidirSwitchInst>& switches, Arena&) {
  InitialiseTerminals(switches);
  FirstPass(switches);
  ChainPropagate(switches);
}

}  // namespace delta
