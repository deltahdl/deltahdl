#include "simulator/net.h"

#include "common/arena.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

namespace delta {

// --- NetStrength combination (§28.12.2 R2) ---

NetStrength CombineAmbiguousStrength(NetStrength a, NetStrength b) {
  auto hi = [](Strength x, Strength y) {
    return static_cast<uint8_t>(x) > static_cast<uint8_t>(y) ? x : y;
  };
  auto lo = [](Strength x, Strength y) {
    return static_cast<uint8_t>(x) < static_cast<uint8_t>(y) ? x : y;
  };
  NetStrength r;
  r.s0_hi = hi(a.s0_hi, b.s0_hi);
  r.s1_hi = hi(a.s1_hi, b.s1_hi);
  r.s0_lo = lo(a.s0_lo, b.s0_lo);
  r.s1_lo = lo(a.s1_lo, b.s1_lo);
  return r;
}

// --- Per-word resolution helpers ---

Logic4Word ResolveWireWord(Logic4Word a, Logic4Word b) {
  // IEEE §28.7 wire/tri resolution table:
  //   z resolves to the other driver; conflicting known bits produce x.
  uint64_t a_z = a.aval & a.bval;
  uint64_t b_z = b.aval & b.bval;
  uint64_t both_z = a_z & b_z;
  uint64_t a_only_z = a_z & ~b_z;
  uint64_t b_only_z = b_z & ~a_z;
  uint64_t neither_z = ~a_z & ~b_z;

  uint64_t a_x = ~a.aval & a.bval;
  uint64_t b_x = ~b.aval & b.bval;
  uint64_t conflict = ~a.bval & ~b.bval & (a.aval ^ b.aval);
  uint64_t unknown = (a_x | b_x | conflict) & neither_z;

  uint64_t res_aval = both_z | (b.aval & a_only_z) | (a.aval & b_only_z) |
                      (a.aval & neither_z & ~unknown);
  uint64_t res_bval =
      both_z | (b.bval & a_only_z) | (a.bval & b_only_z) | unknown;
  return {res_aval, res_bval};
}

Logic4Word ResolveWandWord(Logic4Word a, Logic4Word b) {
  // Wand/triand: AND semantics. 0 dominates, z defers to other driver.
  uint64_t a_z = a.aval & a.bval;
  uint64_t b_z = b.aval & b.bval;
  uint64_t both_z = a_z & b_z;
  uint64_t a_only_z = a_z & ~b_z;
  uint64_t b_only_z = b_z & ~a_z;
  uint64_t neither_z = ~a_z & ~b_z;

  uint64_t a_0 = ~a.aval & ~a.bval;
  uint64_t b_0 = ~b.aval & ~b.bval;
  uint64_t either_0 = (a_0 | b_0) & neither_z;
  uint64_t a_x = ~a.aval & a.bval;
  uint64_t b_x = ~b.aval & b.bval;
  uint64_t either_x = (a_x | b_x) & neither_z & ~either_0;
  uint64_t both_1 = a.aval & ~a.bval & b.aval & ~b.bval & neither_z;

  uint64_t res_aval =
      both_z | (b.aval & a_only_z) | (a.aval & b_only_z) | both_1;
  uint64_t res_bval =
      both_z | (b.bval & a_only_z) | (a.bval & b_only_z) | either_x;
  return {res_aval, res_bval};
}

Logic4Word ResolveWorWord(Logic4Word a, Logic4Word b) {
  // Wor/trior: OR semantics. 1 dominates, z defers to other driver.
  uint64_t a_z = a.aval & a.bval;
  uint64_t b_z = b.aval & b.bval;
  uint64_t both_z = a_z & b_z;
  uint64_t a_only_z = a_z & ~b_z;
  uint64_t b_only_z = b_z & ~a_z;
  uint64_t neither_z = ~a_z & ~b_z;

  uint64_t a_1 = a.aval & ~a.bval;
  uint64_t b_1 = b.aval & ~b.bval;
  uint64_t either_1 = (a_1 | b_1) & neither_z;
  uint64_t a_x = ~a.aval & a.bval;
  uint64_t b_x = ~b.aval & b.bval;
  uint64_t either_x = (a_x | b_x) & neither_z & ~either_1;

  uint64_t res_aval =
      both_z | (b.aval & a_only_z) | (a.aval & b_only_z) | either_1;
  uint64_t res_bval =
      both_z | (b.bval & a_only_z) | (a.bval & b_only_z) | either_x;
  return {res_aval, res_bval};
}

// --- Per-word resolution dispatch ---

static Logic4Word ResolveWord(Logic4Word a, Logic4Word b, NetType type) {
  switch (type) {
    case NetType::kWand:
    case NetType::kTriand:
      return ResolveWandWord(a, b);
    case NetType::kWor:
    case NetType::kTrior:
      return ResolveWorWord(a, b);
    default:
      return ResolveWireWord(a, b);
  }
}

// Fix up z bits for tri0/tri1: replace z with 0 or 1.
static void FixupTriPull(Logic4Vec& result, NetType type) {
  if (type != NetType::kTri0 && type != NetType::kTri1) return;
  for (uint32_t w = 0; w < result.nwords; ++w) {
    uint64_t z_bits = result.words[w].aval & result.words[w].bval;
    if (z_bits == 0) continue;
    result.words[w].bval &= ~z_bits;  // Clear bval → known.
    if (type == NetType::kTri1) {
      result.words[w].aval |= z_bits;  // Set aval → 1.
    } else {
      result.words[w].aval &= ~z_bits;  // Clear aval → 0.
    }
  }
}

// --- Strength-aware per-bit resolution (IEEE §28.12.1) ---

struct BitVal {
  uint8_t val;  // 0, 1, 2=x, 3=z
};

static BitVal GetBitVal(const Logic4Vec& vec, uint32_t bit) {
  uint32_t word = bit / 64;
  uint64_t mask = uint64_t{1} << (bit % 64);
  if (word >= vec.nwords) return {3};  // z
  bool a = (vec.words[word].aval & mask) != 0;
  bool b = (vec.words[word].bval & mask) != 0;
  if (!b && !a) return {0};
  if (!b && a) return {1};
  if (b && !a) return {2};  // x
  return {3};               // z
}

static void SetBit(Logic4Vec& vec, uint32_t bit, uint8_t val) {
  uint32_t word = bit / 64;
  uint64_t mask = uint64_t{1} << (bit % 64);
  if (word >= vec.nwords) return;
  if (val == 0) {
    vec.words[word].aval &= ~mask;
    vec.words[word].bval &= ~mask;
  } else if (val == 1) {
    vec.words[word].aval |= mask;
    vec.words[word].bval &= ~mask;
  } else if (val == 2) {  // x
    vec.words[word].aval &= ~mask;
    vec.words[word].bval |= mask;
  } else {  // z
    vec.words[word].aval |= mask;
    vec.words[word].bval |= mask;
  }
}

static uint8_t EffectiveStrength(uint8_t val, DriverStrength ds) {
  auto s0 = static_cast<uint8_t>(ds.s0);
  auto s1 = static_cast<uint8_t>(ds.s1);
  if (val == 0) return s0;
  if (val == 1) return s1;
  if (val == 2) return (s0 > s1) ? s0 : s1;  // x: max
  return 0;                                  // z: no strength
}

// §28.12.4: 4-valued AND/OR used by wand/triand/wor/trior to resolve
// same-strength conflicts instead of falling back to x.
static uint8_t WiredAnd(uint8_t a, uint8_t b) {
  if (a == 0 || b == 0) return 0;
  if (a == 1 && b == 1) return 1;
  return 2;
}

static uint8_t WiredOr(uint8_t a, uint8_t b) {
  if (a == 1 || b == 1) return 1;
  if (a == 0 && b == 0) return 0;
  return 2;
}

// §28.12.3 rule a/b applied to one side of the strength scale: keep ambig
// levels strictly above Su; lift the per-side lo to max(orig_lo, Su+1) where
// the side survives; otherwise leave the side empty.
static void TrimAmbigSide(Strength a_lo, Strength a_hi, uint8_t su,
                          Strength& r_lo, Strength& r_hi) {
  if (static_cast<uint8_t>(a_hi) <= su) return;
  uint8_t lo_idx = std::max<uint8_t>(static_cast<uint8_t>(a_lo),
                                     static_cast<uint8_t>(su + 1));
  r_lo = static_cast<Strength>(lo_idx);
  r_hi = a_hi;
}

// §28.12.3 rule c: if the !Vu side has a surviving range with lo > Su+1, the
// gap left between the unambig (at Su on the Vu side) and the surviving
// ambig portion is filled by lowering the !Vu lo to Su+1.
static void FillRuleCGap(Strength& r_lo, Strength r_hi, uint8_t su) {
  if (r_hi == Strength::kHighz) return;
  if (static_cast<uint8_t>(r_lo) <= su + 1) return;
  r_lo = static_cast<Strength>(su + 1);
}

// §28.12.3: combine an ambiguous-strength signal with one component of value
// Vu and single strength level Su. Rules a/b/c are applied to each side of
// the strength scale.
static NetStrength CombineAmbigWithUnambig(NetStrength ambig, uint8_t vu,
                                           uint8_t su) {
  NetStrength r;
  TrimAmbigSide(ambig.s0_lo, ambig.s0_hi, su, r.s0_lo, r.s0_hi);
  TrimAmbigSide(ambig.s1_lo, ambig.s1_hi, su, r.s1_lo, r.s1_hi);

  auto s_su = static_cast<Strength>(su);
  Strength& vu_hi = (vu == 0) ? r.s0_hi : r.s1_hi;
  Strength& vu_lo = (vu == 0) ? r.s0_lo : r.s1_lo;
  if (vu_hi == Strength::kHighz) vu_hi = s_su;
  vu_lo = s_su;

  Strength& opp_hi = (vu == 0) ? r.s1_hi : r.s0_hi;
  Strength& opp_lo = (vu == 0) ? r.s1_lo : r.s0_lo;
  FillRuleCGap(opp_lo, opp_hi, su);
  return r;
}

// Decode a driver bit into the 0/1/2=x/3=z slot for bit 0. Pulled out of
// the iteration loops to shrink their cognitive complexity.
static uint8_t DriverBit0Val(const Logic4Vec& drv) {
  uint64_t mask = 1;
  bool a = (drv.words[0].aval & mask) != 0;
  bool b = (drv.words[0].bval & mask) != 0;
  if (!b && !a) return 0;
  if (!b && a) return 1;
  if (b && !a) return 2;
  return 3;
}

// §28.12.3: locate the strongest unambig driver (value 0 or 1) whose
// strength sits strictly below the conflict strength. Returns true and sets
// vu/su when one exists; returns false otherwise.
static bool FindWeakerUnambig(const std::vector<Logic4Vec>& drivers,
                              const std::vector<DriverStrength>& strengths,
                              uint8_t max_str, uint8_t& vu, uint8_t& su) {
  vu = 3;
  su = 0;
  for (size_t d = 0; d < drivers.size(); ++d) {
    uint8_t val = DriverBit0Val(drivers[d]);
    if (val > 1) continue;
    uint8_t str = EffectiveStrength(val, strengths[d]);
    if (str < max_str && str > su) {
      su = str;
      vu = val;
    }
  }
  return vu < 2 && su > 0;
}

struct MaxTracker {
  uint8_t str = 0;
  uint8_t val = 3;
  bool conflict = false;
};

// Update the running tracker for one driver's (val, str) contribution,
// applying §28.12.4 wand/wor when applicable.
static void FoldDriverIntoMax(uint8_t val, uint8_t str, NetType net_type,
                              MaxTracker& m) {
  if (str > m.str) {
    m.str = str;
    m.val = val;
    m.conflict = false;
    return;
  }
  if (str != m.str || val == m.val) return;
  if (net_type == NetType::kWand || net_type == NetType::kTriand) {
    m.val = WiredAnd(m.val, val);
  } else if (net_type == NetType::kWor || net_type == NetType::kTrior) {
    m.val = WiredOr(m.val, val);
  } else {
    m.conflict = true;
  }
}

// §28.12 R1 at bit 0: pick the dominant (value, strength) across drivers and
// populate the net's resolved_strength. The unambiguous branch records a
// single level on the value's side. The ambiguous branch — §28.12.2 R1 —
// fires when two drivers tie at the max strength with opposite values: the
// value collapses to x and the result must carry the shared strength level
// on both sides of the scale together with every smaller level. Wand/wor
// resolve same-strength disagreements through §28.12.4's AND/OR and stay
// unambiguous. After §28.12.2 produces the ambig signal, §28.12.3 folds in
// the strongest unambig driver below the conflict strength.
static void ComputeSingleBitStrength(
    const std::vector<Logic4Vec>& drivers,
    const std::vector<DriverStrength>& strengths, NetStrength& out,
    NetType net_type) {
  MaxTracker m;
  for (size_t d = 0; d < drivers.size(); ++d) {
    uint8_t val = DriverBit0Val(drivers[d]);
    if (val == 3) continue;
    uint8_t str = EffectiveStrength(val, strengths[d]);
    FoldDriverIntoMax(val, str, net_type, m);
  }
  out = NetStrength{};
  if (m.val == 3) return;
  auto s = static_cast<Strength>(m.str);
  if (m.conflict) {
    out.s0_hi = s;
    out.s1_hi = s;
    uint8_t su = 0;
    uint8_t vu = 3;
    if (FindWeakerUnambig(drivers, strengths, m.str, vu, su)) {
      out = CombineAmbigWithUnambig(out, vu, su);
    }
    return;
  }
  if (m.val == 0) {
    out.s0_hi = out.s0_lo = s;
  } else if (m.val == 1) {
    out.s1_hi = out.s1_lo = s;
  } else if (m.val == 2 && (net_type == NetType::kWand ||
                            net_type == NetType::kTriand ||
                            net_type == NetType::kWor ||
                            net_type == NetType::kTrior)) {
    // §28.12.4: when wired AND/OR produces an x (e.g., wand of 1 and x), the
    // result carries the strength of the combined signals. x lives on both
    // sides of the strength scale, so record the same single level on each.
    out.s0_hi = out.s0_lo = s;
    out.s1_hi = out.s1_lo = s;
  }
}

static void ResolveStrengthBit(const std::vector<Logic4Vec>& drivers,
                               const std::vector<DriverStrength>& strengths,
                               Logic4Vec& result, uint32_t bit,
                               NetType net_type) {
  uint8_t max_str = 0;
  uint8_t max_val = 3;  // z
  bool conflict = false;
  for (size_t d = 0; d < drivers.size(); ++d) {
    auto bv = GetBitVal(drivers[d], bit);
    if (bv.val == 3) continue;  // z: no contribution
    uint8_t str = EffectiveStrength(bv.val, strengths[d]);
    if (str > max_str) {
      max_str = str;
      max_val = bv.val;
      conflict = false;
    } else if (str == max_str && bv.val != max_val) {
      // §28.12.4: wired-logic net types resolve same-strength value
      // disagreements by applying AND/OR over the driver values rather than
      // producing x. For plain wire/tri/trireg the conflict propagates as x.
      if (net_type == NetType::kWand || net_type == NetType::kTriand) {
        max_val = WiredAnd(max_val, bv.val);
      } else if (net_type == NetType::kWor || net_type == NetType::kTrior) {
        max_val = WiredOr(max_val, bv.val);
      } else {
        conflict = true;
      }
    }
  }
  SetBit(result, bit, conflict ? 2 : max_val);
}

// --- Helpers ---

static bool AllDriversZ(const std::vector<Logic4Vec>& drivers) {
  for (const auto& drv : drivers) {
    for (uint32_t w = 0; w < drv.nwords; ++w) {
      if (drv.words[w].bval != ~uint64_t{0} ||
          drv.words[w].aval != ~uint64_t{0}) {
        return false;
      }
    }
  }
  return true;
}

static void SetAllX(Logic4Vec& val) {
  for (uint32_t w = 0; w < val.nwords; ++w) {
    val.words[w] = {0, ~uint64_t{0}};
  }
}

// §6.6.4.2: Schedule charge decay event with generation counter.
static void ScheduleDecay(Net& net, Scheduler* sched) {
  uint64_t gen = ++net.decay_generation;
  auto* event = sched->GetEventPool().Acquire();
  event->callback = [&net, gen]() {
    if (net.decay_generation != gen) return;
    SetAllX(net.resolved->value);
    net.resolved->NotifyWatchers();
  };
  auto time = sched->CurrentTime();
  time.ticks += net.decay_ticks;
  sched->ScheduleEvent(time, Region::kActive, event);
}

// §28.15.1: With no overriding source, a tri0 net pulls to 0 at pull strength
// and a tri1 net pulls to 1 at pull strength. "No overriding source" covers
// both an empty driver list and drivers contributing only z.
static bool ResolveTriPullDefault(Net& net, Arena& arena) {
  if (net.type != NetType::kTri0 && net.type != NetType::kTri1) return false;
  if (!net.drivers.empty() && !AllDriversZ(net.drivers)) return false;

  auto result = MakeLogic4Vec(arena, net.resolved->value.width);
  uint64_t fill = (net.type == NetType::kTri1) ? ~uint64_t{0} : 0;
  for (uint32_t w = 0; w < result.nwords; ++w) {
    result.words[w] = {fill, 0};
  }
  net.resolved->value = result;
  net.resolved_strength = NetStrength{};
  if (net.type == NetType::kTri0) {
    net.resolved_strength.s0_hi = Strength::kPull;
    net.resolved_strength.s0_lo = Strength::kPull;
  } else {
    net.resolved_strength.s1_hi = Strength::kPull;
    net.resolved_strength.s1_lo = Strength::kPull;
  }
  net.resolved->NotifyWatchers();
  return true;
}

// §6.6.6/§6.6.4/§28.15.1: Handle supply nets, trireg charge retention, and
// tri0/tri1 pull defaults. Returns true if the net type was handled
// (caller should return early).
static bool ResolveSpecialNet(Net& net, Arena& arena, Scheduler* sched) {
  if (net.type == NetType::kSupply0) {
    net.resolved->value = MakeLogic4VecVal(arena, net.resolved->value.width, 0);
    net.resolved->NotifyWatchers();
    return true;
  }
  if (net.type == NetType::kSupply1) {
    auto result = MakeLogic4Vec(arena, net.resolved->value.width);
    for (uint32_t w = 0; w < result.nwords; ++w) {
      result.words[w] = {~uint64_t{0}, 0};
    }
    net.resolved->value = result;
    net.resolved->NotifyWatchers();
    return true;
  }
  if (net.type == NetType::kTrireg && AllDriversZ(net.drivers)) {
    if (net.decay_ticks > 0 && sched != nullptr) {
      ScheduleDecay(net, sched);
    }
    net.resolved->NotifyWatchers();
    return true;
  }
  if (ResolveTriPullDefault(net, arena)) return true;
  return false;
}

// --- Net::Resolve ---

bool Net::InCapacitiveState() const {
  return type == NetType::kTrireg && AllDriversZ(drivers);
}

void Net::Resolve(Arena& arena, Scheduler* sched) {
  if (!resolved) return;
  // §6.7.3 / §28.15.1: User-defined nettypes and tri0/tri1 must resolve
  // even with no drivers — the latter pull to their default value/strength.
  bool needs_resolution_when_undriven =
      is_user_nettype || type == NetType::kTri0 || type == NetType::kTri1;
  if (drivers.empty() && !needs_resolution_when_undriven) return;

  // Cancel pending decay when trireg exits capacitive state.
  if (type == NetType::kTrireg && !AllDriversZ(drivers)) {
    ++decay_generation;
  }

  if (ResolveSpecialNet(*this, arena, sched)) return;

  // §28.12: user-defined nettypes shall not carry strength levels, so any
  // per-driver strength on such a net is ignored — skip the strength-aware
  // path and fall through to value-only resolution.
  if (!is_user_nettype && !driver_strengths.empty()) {
    auto result = MakeLogic4Vec(arena, resolved->value.width);
    for (uint32_t b = 0; b < result.width; ++b) {
      ResolveStrengthBit(drivers, driver_strengths, result, b, type);
    }
    FixupTriPull(result, type);
    resolved->value = result;
    ComputeSingleBitStrength(drivers, driver_strengths, resolved_strength,
                             type);
    resolved->NotifyWatchers();
    return;
  }

  if (drivers.size() == 1) {
    resolved->value = drivers[0];
    FixupTriPull(resolved->value, type);
    resolved->NotifyWatchers();
    return;
  }

  // Fold drivers pairwise using the appropriate resolution function.
  Logic4Vec result = drivers[0];
  for (size_t i = 1; i < drivers.size(); ++i) {
    auto combined = MakeLogic4Vec(arena, result.width);
    for (uint32_t w = 0; w < result.nwords; ++w) {
      combined.words[w] =
          ResolveWord(result.words[w], drivers[i].words[w], type);
    }
    result = combined;
  }
  FixupTriPull(result, type);
  resolved->value = result;
  resolved->NotifyWatchers();
}

// --- §6.6.4.1: Capacitive network charge propagation ---

static bool ValuesEqual(const Logic4Vec& a, const Logic4Vec& b) {
  uint32_t n = (a.nwords < b.nwords) ? a.nwords : b.nwords;
  for (uint32_t w = 0; w < n; ++w) {
    if (a.words[w].aval != b.words[w].aval) return false;
    if (a.words[w].bval != b.words[w].bval) return false;
  }
  return true;
}

void PropagateCharge(Net& a, Net& b) {
  if (!a.InCapacitiveState() || !b.InCapacitiveState()) return;
  auto sa = static_cast<uint8_t>(a.charge_strength);
  auto sb = static_cast<uint8_t>(b.charge_strength);
  if (sa > sb) {
    b.resolved->value = a.resolved->value;
    b.charge_strength = a.charge_strength;  // §6.6.4.1: Share charge strength.
    b.resolved->NotifyWatchers();
  } else if (sb > sa) {
    a.resolved->value = b.resolved->value;
    a.charge_strength = b.charge_strength;  // §6.6.4.1: Share charge strength.
    a.resolved->NotifyWatchers();
  } else if (!ValuesEqual(a.resolved->value, b.resolved->value)) {
    SetAllX(a.resolved->value);
    SetAllX(b.resolved->value);
    a.resolved->NotifyWatchers();
    b.resolved->NotifyWatchers();
  }
}

void DisconnectCharge(Net& net) {
  net.charge_strength = net.base_charge_strength;
}

}  // namespace delta
