#include "simulator/switch_network.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/statement_assign.h"
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

// §28.13: a nonresistive bidirectional switch (tran, tranif0, tranif1) does not
// affect the strength of a signal crossing between its terminals, except that a
// supply strength is reduced to a strong strength -- exactly
// ReduceNonresistive.
//
// §28.14: the resistive variants (rtran, rtranif0, rtranif1) instead knock
// every strength level down one step per Table 28-8, exactly ReduceResistive --
// the same reduction the resistive unidirectional switches apply. Selecting
// between the two by switch flavor lets both share the strength-reduction
// functions.
//
// §28.8: there shall be no strength reduction in bidirectional switches
// connecting user-defined net types. Such a switch passes the source strength
// unchanged regardless of whether it is a resistive (r-prefixed) variant, so
// the user-defined-net case bypasses both the §28.13 and §28.14 reductions.
void PassStrengthAcross(Net& dest, const Net& src, BidirSwitchKind kind,
                        bool user_defined_nets) {
  // What the switch passes across is the strength the source net reports, which
  // is one strength for the whole of the destination however the destination's
  // own bits last resolved. Anything Net::Resolve recorded per bit there is
  // therefore no longer the answer, and dropping it leaves Net::BitStrength
  // reading the strength written here.
  dest.bit_strengths.clear();
  if (user_defined_nets) {
    dest.resolved_strength = src.resolved_strength;
    return;
  }
  Strength (*reduce)(Strength) =
      IsNonresistiveBidir(kind) ? &ReduceNonresistive : &ReduceResistive;
  NetStrength s = src.resolved_strength;
  s.s0_hi = reduce(s.s0_hi);
  s.s0_lo = reduce(s.s0_lo);
  s.s1_hi = reduce(s.s1_hi);
  s.s1_lo = reduce(s.s1_lo);
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

namespace {

// Which group resolution is under way: whether one is, the member it is
// resolving at the moment, and whether a net of a group was resolved from
// outside while it ran, which a write a member's watchers made does.
struct GroupGuard {
  bool active = false;
  bool dirty = false;
  const Net* resolving = nullptr;
};

GroupGuard& Guard() {
  static GroupGuard guard;
  return guard;
}

// §28.8 and §4.9.5: a switch whose control is x or z joins nets of built-in
// net types as though it were on and off both, and nets of user-defined net
// types as though it were off.
bool LinkConducts(const SwitchLink& link) {
  if (link.other == nullptr || link.sw == nullptr) return false;
  if (link.sw->state == BidirSwitchState::kOn) return true;
  return link.sw->state == BidirSwitchState::kUnknown &&
         !link.sw->user_defined_nets;
}

// Every net a switch of any state joins `start` to, `start` first.
std::vector<Net*> SwitchGroupOf(Net& start) {
  std::vector<Net*> members{&start};
  for (size_t i = 0; i < members.size(); ++i) {
    for (const SwitchLink& link : members[i]->switch_links) {
      if (link.other != nullptr && std::find(members.begin(), members.end(),
                                             link.other) == members.end()) {
        members.push_back(link.other);
      }
    }
  }
  return members;
}

// One net reached from a member across conducting switches: the index of the
// net it was reached from, and the switch it was reached across.
struct Reached {
  Net* net;
  size_t from;
  const SwitchLink* link;
};

// §10.11: a link joining bits (SwitchLink::bit_map) maps the bits of the
// member it belongs to alone, so it is followed from the member and no
// further; LowerBitAlias links every net sharing a bit with the member to it
// directly.
bool FollowsFrom(const SwitchLink& link, const Reached& from, size_t i) {
  if (from.link != nullptr && from.link->bit_map != nullptr) return false;
  return link.bit_map == nullptr || i == 0;
}

std::vector<Reached> ReachAcrossConducting(Net& member) {
  std::vector<Reached> reached{{&member, 0, nullptr}};
  for (size_t i = 0; i < reached.size(); ++i) {
    for (const SwitchLink& link : reached[i].net->switch_links) {
      if (!LinkConducts(link) || !FollowsFrom(link, reached[i], i)) continue;
      bool seen = std::any_of(
          reached.begin(), reached.end(),
          [&link](const Reached& r) { return r.net == link.other; });
      if (!seen) reached.push_back({link.other, i, &link});
    }
  }
  return reached;
}

Logic4Vec ConstantOf(uint32_t width, bool one, Arena& arena) {
  Logic4Vec v = MakeLogic4Vec(arena, width);
  for (uint32_t w = 0; w < v.nwords; ++w) {
    v.words[w].aval = one ? WordMaskWithinWidth(width, w) : 0;
    v.words[w].bval = 0;
  }
  return v;
}

// What a net contributes to the nets joined to it: its drivers at their
// strengths, and the constant a supply0 or supply1 net (§28.15.3) or a tri0
// or tri1 net (§6.6.5) carries without one.
void OwnSources(const Net& net, Arena& arena, std::vector<Logic4Vec>& values,
                std::vector<DriverStrength>& strengths) {
  values = net.drivers;
  strengths = net.driver_strengths;
  strengths.resize(values.size());
  uint32_t width = net.resolved->value.width;
  auto add = [&](bool one, Strength level) {
    values.push_back(ConstantOf(width, one, arena));
    strengths.push_back({level, level});
  };
  if (net.type == NetType::kSupply0) add(false, Strength::kSupply);
  if (net.type == NetType::kSupply1) add(true, Strength::kSupply);
  if (net.type == NetType::kTri0) add(false, Strength::kPull);
  if (net.type == NetType::kTri1) add(true, Strength::kPull);
}

// §28.13 and §28.14: a signal crossing tran, tranif0 or tranif1 keeps its
// strength but for supply becoming strong, and one crossing rtran, rtranif0 or
// rtranif1 is reduced by Table 28-8; §28.8 has no reduction across a switch
// joining nets of user-defined net types.
DriverStrength ReduceAcross(DriverStrength ds, const SwitchLink& link) {
  if (link.sw->user_defined_nets || link.sw->is_alias) return ds;
  Strength (*reduce)(Strength) = IsNonresistiveBidir(link.sw->kind)
                                     ? &ReduceNonresistive
                                     : &ReduceResistive;
  return {reduce(ds.s0), reduce(ds.s1)};
}

// A driver's value as seen through a switch whose control is x or z: each 0
// bit is L and each 1 bit H, the value or z (§4.9.5), which a driver spells
// as x with the other side of its strength at the high-impedance level, so
// the 0 bits, the 1 bits and the x bits travel as three drivers.
void AppendThroughUnknown(Net& member, const Logic4Vec& v, DriverStrength ds,
                          Arena& arena) {
  Logic4Vec parts[3] = {MakeLogic4Vec(arena, v.width),
                        MakeLogic4Vec(arena, v.width),
                        MakeLogic4Vec(arena, v.width)};
  bool any[3] = {false, false, false};
  for (uint32_t w = 0; w < v.nwords; ++w) {
    uint64_t mask = WordMaskWithinWidth(v.width, w);
    uint64_t a = v.words[w].aval;
    uint64_t b = v.words[w].bval;
    uint64_t bits[3] = {~a & ~b & mask, a & ~b & mask, a & b & mask};
    for (int k = 0; k < 3; ++k) {
      parts[k].words[w] = {bits[k], mask};
      any[k] = any[k] || bits[k] != 0;
    }
  }
  DriverStrength sides[3] = {
      {ds.s0, Strength::kHighz}, {Strength::kHighz, ds.s1}, ds};
  for (int k = 0; k < 3; ++k) {
    if (!any[k]) continue;
    member.switch_drivers.push_back(parts[k]);
    member.switch_strengths.push_back(sides[k]);
  }
}

// A source value as it lands on a member `width` bits wide: resized to it, or,
// across a link joining bits (§10.11), each bit the link maps placed at the
// member's bit it is one with and every other bit z, which drives nothing.
Logic4Vec ArrivingValue(const Logic4Vec& value, const SwitchLink* link,
                        uint32_t width, Arena& arena) {
  if (link == nullptr || link->bit_map == nullptr)
    return ResizeToWidth(value, width, arena);
  Logic4Vec v = MakeAllHighZ(arena, width);
  for (const auto& [mine, theirs] : *link->bit_map)
    DepositBitField(v, mine, ExtractBitField(arena, value, theirs, 1), 1);
  return v;
}

// The sources of `reached[j]` as they arrive at the member, reduced across
// every switch on the way back and made L or H by one whose control is x or
// z.
void AppendReachedSources(Net& member, const std::vector<Reached>& reached,
                          size_t j, Arena& arena) {
  std::vector<Logic4Vec> values;
  std::vector<DriverStrength> strengths;
  OwnSources(*reached[j].net, arena, values, strengths);
  uint32_t width = member.resolved->value.width;
  for (size_t d = 0; d < values.size(); ++d) {
    DriverStrength ds = strengths[d];
    bool unknown = false;
    for (size_t k = j; reached[k].link != nullptr; k = reached[k].from) {
      ds = ReduceAcross(ds, *reached[k].link);
      unknown =
          unknown || reached[k].link->sw->state == BidirSwitchState::kUnknown;
    }
    Logic4Vec v = ArrivingValue(values[d], reached[j].link, width, arena);
    if (unknown) {
      AppendThroughUnknown(member, v, ds, arena);
    } else {
      member.switch_drivers.push_back(v);
      member.switch_strengths.push_back(ds);
    }
  }
}

void GatherSwitchDrivers(Net& member, Arena& arena) {
  member.switch_drivers.clear();
  member.switch_strengths.clear();
  if (member.resolved == nullptr) return;
  std::vector<Reached> reached = ReachAcrossConducting(member);
  for (size_t j = 1; j < reached.size(); ++j) {
    if (reached[j].net->resolved == nullptr) continue;
    AppendReachedSources(member, reached, j, arena);
  }
}

bool CarriesItsOwnSource(const Net& net) {
  return net.type == NetType::kSupply0 || net.type == NetType::kSupply1 ||
         net.type == NetType::kTri0 || net.type == NetType::kTri1;
}

// §6.6: "If no driver is connected to a net, its value shall be
// high-impedance (z)", which a net left with nothing reaching it across its
// switches is.
void LeaveUndriven(Net& net, Arena& arena) {
  net.resolved_strength = NetStrength{};
  net.bit_strengths.clear();
  Logic4Vec& v = net.resolved->value;
  bool already_z = true;
  for (uint32_t w = 0; w < v.nwords; ++w) {
    uint64_t mask = WordMaskWithinWidth(v.width, w);
    already_z = already_z && (v.words[w].aval & mask) == 0 &&
                (v.words[w].bval & mask) == mask;
  }
  if (already_z) return;
  v = MakeAllHighZ(arena, v.width);
  net.resolved->NotifyWatchers();
}

void ResolveMember(Net& member, Arena& arena, Scheduler* sched) {
  if (member.resolved == nullptr) return;
  if (member.drivers.empty() && member.switch_drivers.empty() &&
      !CarriesItsOwnSource(member)) {
    LeaveUndriven(member, arena);
    return;
  }
  Guard().resolving = &member;
  member.Resolve(arena, sched);
  Guard().resolving = nullptr;
}

// Enough passes for a change a member's watchers made to settle; each pass
// gathers every member's sources again before resolving any of them.
constexpr int kMaxGroupPasses = 8;

}  // namespace

uint8_t BidirSwitchStateFor(BidirSwitchKind kind, Logic4Word control) {
  if (BidirSwitchControlIsUnknown(kind, control)) {
    return BidirSwitchState::kUnknown;
  }
  return BidirSwitchConducts(kind, control) ? BidirSwitchState::kOn
                                            : BidirSwitchState::kOff;
}

bool ResolveSwitchGroup(Net& net, Arena& arena, Scheduler* sched) {
  GroupGuard& guard = Guard();
  if (guard.resolving == &net) return false;
  if (guard.active) {
    guard.dirty = true;
    return false;
  }
  guard.active = true;
  std::vector<Net*> members = SwitchGroupOf(net);
  for (int pass = 0; pass < kMaxGroupPasses; ++pass) {
    guard.dirty = false;
    for (Net* member : members) GatherSwitchDrivers(*member, arena);
    for (Net* member : members) ResolveMember(*member, arena, sched);
    if (!guard.dirty) break;
  }
  guard.active = false;
  return true;
}

}  // namespace delta
