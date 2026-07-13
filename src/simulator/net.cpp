#include "simulator/net.h"

#include "common/arena.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

namespace delta {

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

namespace {

struct StrengthComponent {
  uint8_t val;
  uint8_t level;
};

static void CollectComponents(NetStrength s,
                              std::vector<StrengthComponent>& out) {
  if (s.s0_hi != Strength::kHighz) {
    for (auto lvl = static_cast<uint8_t>(s.s0_lo);
         lvl <= static_cast<uint8_t>(s.s0_hi); ++lvl) {
      out.push_back({0, lvl});
    }
  }
  if (s.s1_hi != Strength::kHighz) {
    for (auto lvl = static_cast<uint8_t>(s.s1_lo);
         lvl <= static_cast<uint8_t>(s.s1_hi); ++lvl) {
      out.push_back({1, lvl});
    }
  }
}

static StrengthComponent ReduceWiredPair(StrengthComponent a,
                                         StrengthComponent b,
                                         WiredLogicKind kind) {
  if (a.level != b.level) {
    return (a.level > b.level) ? a : b;
  }
  if (a.val == b.val) {
    return a;
  }
  uint8_t resolved = (kind == WiredLogicKind::kAnd) ? std::min(a.val, b.val)
                                                    : std::max(a.val, b.val);
  return {resolved, a.level};
}

struct WiredLevelRange {
  bool present = false;
  uint8_t min = 255;
  uint8_t max = 0;
};

static void FoldWiredComponent(StrengthComponent rc, WiredLevelRange& side0,
                               WiredLevelRange& side1) {
  WiredLevelRange& side = (rc.val == 0) ? side0 : side1;
  side.present = true;
  if (rc.level < side.min) side.min = rc.level;
  if (rc.level > side.max) side.max = rc.level;
}

static void ApplyWiredRange(const WiredLevelRange& side, Strength& lo,
                            Strength& hi) {
  if (!side.present) return;
  lo = static_cast<Strength>(side.min);
  hi = static_cast<Strength>(side.max);
}

}  // namespace

NetStrength CombineWiredLogicAmbiguous(NetStrength a, NetStrength b,
                                       WiredLogicKind kind) {
  std::vector<StrengthComponent> ca;
  std::vector<StrengthComponent> cb;
  CollectComponents(a, ca);
  CollectComponents(b, cb);

  NetStrength r;
  if (ca.empty() || cb.empty()) return r;

  WiredLevelRange side0;
  WiredLevelRange side1;
  for (const auto& x : ca) {
    for (const auto& y : cb) {
      FoldWiredComponent(ReduceWiredPair(x, y, kind), side0, side1);
    }
  }
  ApplyWiredRange(side0, r.s0_lo, r.s0_hi);
  ApplyWiredRange(side1, r.s1_lo, r.s1_hi);
  return r;
}

// Net resolution under the canonical 4-state encoding (LRM Figure 38-8):
// z=(aval=0,bval=1), x=(aval=1,bval=1). A z bit is detected as ~aval & bval and
// an x bit as aval & bval. A z result contributes only to res_bval (its aval is
// 0); an x result sets both res_aval and res_bval.
Logic4Word ResolveWireWord(Logic4Word a, Logic4Word b) {
  uint64_t a_z = ~a.aval & a.bval;
  uint64_t b_z = ~b.aval & b.bval;
  uint64_t both_z = a_z & b_z;
  uint64_t a_only_z = a_z & ~b_z;
  uint64_t b_only_z = b_z & ~a_z;
  uint64_t neither_z = ~a_z & ~b_z;

  uint64_t a_x = a.aval & a.bval;
  uint64_t b_x = b.aval & b.bval;
  uint64_t conflict = ~a.bval & ~b.bval & (a.aval ^ b.aval);
  uint64_t unknown = (a_x | b_x | conflict) & neither_z;

  uint64_t res_aval = (b.aval & a_only_z) | (a.aval & b_only_z) |
                      (a.aval & neither_z & ~unknown) | unknown;
  uint64_t res_bval =
      both_z | (b.bval & a_only_z) | (a.bval & b_only_z) | unknown;
  return {res_aval, res_bval};
}

Logic4Word ResolveWandWord(Logic4Word a, Logic4Word b) {
  uint64_t a_z = ~a.aval & a.bval;
  uint64_t b_z = ~b.aval & b.bval;
  uint64_t both_z = a_z & b_z;
  uint64_t a_only_z = a_z & ~b_z;
  uint64_t b_only_z = b_z & ~a_z;
  uint64_t neither_z = ~a_z & ~b_z;

  uint64_t a_0 = ~a.aval & ~a.bval;
  uint64_t b_0 = ~b.aval & ~b.bval;
  uint64_t either_0 = (a_0 | b_0) & neither_z;
  uint64_t a_x = a.aval & a.bval;
  uint64_t b_x = b.aval & b.bval;
  uint64_t either_x = (a_x | b_x) & neither_z & ~either_0;
  uint64_t both_1 = a.aval & ~a.bval & b.aval & ~b.bval & neither_z;

  uint64_t res_aval =
      (b.aval & a_only_z) | (a.aval & b_only_z) | both_1 | either_x;
  uint64_t res_bval =
      both_z | (b.bval & a_only_z) | (a.bval & b_only_z) | either_x;
  return {res_aval, res_bval};
}

Logic4Word ResolveWorWord(Logic4Word a, Logic4Word b) {
  uint64_t a_z = ~a.aval & a.bval;
  uint64_t b_z = ~b.aval & b.bval;
  uint64_t both_z = a_z & b_z;
  uint64_t a_only_z = a_z & ~b_z;
  uint64_t b_only_z = b_z & ~a_z;
  uint64_t neither_z = ~a_z & ~b_z;

  uint64_t a_1 = a.aval & ~a.bval;
  uint64_t b_1 = b.aval & ~b.bval;
  uint64_t either_1 = (a_1 | b_1) & neither_z;
  uint64_t a_x = a.aval & a.bval;
  uint64_t b_x = b.aval & b.bval;
  uint64_t either_x = (a_x | b_x) & neither_z & ~either_1;

  uint64_t res_aval =
      (b.aval & a_only_z) | (a.aval & b_only_z) | either_1 | either_x;
  uint64_t res_bval =
      both_z | (b.bval & a_only_z) | (a.bval & b_only_z) | either_x;
  return {res_aval, res_bval};
}

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

// Fill every valid bit of a vector with a constant 0 or 1, leaving the unused
// high bits of the final partial word clear. Callers that write a raw ~0 fill
// would otherwise pollute those bits, and ToUint64 reads the whole word.
static void FillConstBit(Logic4Vec& vec, bool one) {
  for (uint32_t w = 0; w < vec.nwords; ++w) {
    uint64_t word = one ? ~uint64_t{0} : 0;
    uint32_t bits = vec.width - w * 64;
    if (bits < 64) word &= (uint64_t{1} << bits) - 1;
    vec.words[w] = {word, 0};
  }
}

static void FixupTriPull(Logic4Vec& result, NetType type) {
  if (type != NetType::kTri0 && type != NetType::kTri1) return;
  for (uint32_t w = 0; w < result.nwords; ++w) {
    uint64_t z_bits = ~result.words[w].aval & result.words[w].bval;
    if (z_bits == 0) continue;
    result.words[w].bval &= ~z_bits;
    if (type == NetType::kTri1) {
      result.words[w].aval |= z_bits;
    } else {
      result.words[w].aval &= ~z_bits;
    }
  }
}

struct BitVal {
  uint8_t val;
};

static BitVal GetBitVal(const Logic4Vec& vec, uint32_t bit) {
  uint32_t word = bit / 64;
  uint64_t mask = uint64_t{1} << (bit % 64);
  if (word >= vec.nwords) return {3};
  bool a = (vec.words[word].aval & mask) != 0;
  bool b = (vec.words[word].bval & mask) != 0;
  if (!b && !a) return {0};
  if (!b && a) return {1};
  if (b && a) return {2};  // x = (aval=1, bval=1)
  return {3};              // z = (aval=0, bval=1)
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
  } else if (val == 2) {  // x = (aval=1, bval=1)
    vec.words[word].aval |= mask;
    vec.words[word].bval |= mask;
  } else {  // z = (aval=0, bval=1)
    vec.words[word].aval &= ~mask;
    vec.words[word].bval |= mask;
  }
}

static uint8_t EffectiveStrength(uint8_t val, DriverStrength ds) {
  auto s0 = static_cast<uint8_t>(ds.s0);
  auto s1 = static_cast<uint8_t>(ds.s1);
  if (val == 0) return s0;
  if (val == 1) return s1;
  if (val == 2) return (s0 > s1) ? s0 : s1;
  return 0;
}

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

static void TrimAmbigSide(Strength a_lo, Strength a_hi, uint8_t su,
                          Strength& r_lo, Strength& r_hi) {
  if (static_cast<uint8_t>(a_hi) <= su) return;
  uint8_t lo_idx = std::max<uint8_t>(static_cast<uint8_t>(a_lo),
                                     static_cast<uint8_t>(su + 1));
  r_lo = static_cast<Strength>(lo_idx);
  r_hi = a_hi;
}

static void FillRuleCGap(Strength& r_lo, Strength r_hi, uint8_t su) {
  if (r_hi == Strength::kHighz) return;
  if (static_cast<uint8_t>(r_lo) <= su + 1) return;
  r_lo = static_cast<Strength>(su + 1);
}

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

static uint8_t DriverBit0Val(const Logic4Vec& drv) {
  uint64_t mask = 1;
  bool a = (drv.words[0].aval & mask) != 0;
  bool b = (drv.words[0].bval & mask) != 0;
  // Canonical Convention A, matching GetBitVal and the val-code consumers
  // (WiredAnd/WiredOr/EffectiveStrength): x = (aval=1, bval=1) -> 2, which
  // carries drive strength; z = (aval=0, bval=1) -> 3, which is high impedance.
  if (!b && !a) return 0;
  if (!b && a) return 1;
  if (b && a) return 2;  // x
  return 3;              // z
}

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
  } else if (m.val == 2 &&
             (net_type == NetType::kWand || net_type == NetType::kTriand ||
              net_type == NetType::kWor || net_type == NetType::kTrior)) {
    out.s0_hi = out.s0_lo = s;
    out.s1_hi = out.s1_lo = s;
  }
}

static void ResolveStrengthBit(const std::vector<Logic4Vec>& drivers,
                               const std::vector<DriverStrength>& strengths,
                               Logic4Vec& result, uint32_t bit,
                               NetType net_type) {
  uint8_t max_str = 0;
  uint8_t max_val = 3;
  bool conflict = false;
  for (size_t d = 0; d < drivers.size(); ++d) {
    auto bv = GetBitVal(drivers[d], bit);
    if (bv.val == 3) continue;
    uint8_t str = EffectiveStrength(bv.val, strengths[d]);
    if (str > max_str) {
      max_str = str;
      max_val = bv.val;
      conflict = false;
    } else if (str == max_str && bv.val != max_val) {
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

static bool AllDriversZ(const std::vector<Logic4Vec>& drivers) {
  // z = (aval=0, bval=1): a word is all-z iff every bval bit is set and every
  // aval bit is clear.
  for (const auto& drv : drivers) {
    for (uint32_t w = 0; w < drv.nwords; ++w) {
      if (drv.words[w].bval != ~uint64_t{0} || drv.words[w].aval != 0) {
        return false;
      }
    }
  }
  return true;
}

static void SetAllX(Logic4Vec& val) {
  for (uint32_t w = 0; w < val.nwords; ++w) {
    val.words[w] = {~uint64_t{0}, ~uint64_t{0}};  // x = (aval=1, bval=1)
  }
}

static void DecayKnownBitsToX(Logic4Vec& val) {
  for (uint32_t w = 0; w < val.nwords; ++w) {
    uint64_t known = ~val.words[w].bval;
    val.words[w].aval |= known;  // decayed bit becomes x = (aval=1, bval=1)
    val.words[w].bval |= known;
  }
}

static void ScheduleDecay(Net& net, Scheduler* sched) {
  uint64_t gen = ++net.decay_generation;
  auto* event = sched->GetEventPool().Acquire();

  event->kind = EventKind::kUpdate;
  event->callback = [&net, gen]() {
    if (net.decay_generation != gen) return;
    DecayKnownBitsToX(net.resolved->value);
    net.resolved->NotifyWatchers();
  };
  auto time = sched->CurrentTime();
  time.ticks += net.decay_ticks;
  sched->ScheduleEvent(time, Region::kActive, event);
}

static bool ResolveTriPullDefault(Net& net, Arena& arena) {
  if (net.type != NetType::kTri0 && net.type != NetType::kTri1) return false;
  if (!net.drivers.empty() && !AllDriversZ(net.drivers)) return false;

  auto result = MakeLogic4Vec(arena, net.resolved->value.width);
  FillConstBit(result, net.type == NetType::kTri1);
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

// §6.6.6: supply0 and supply1 nets model the power supplies in a circuit and
// shall carry supply strength. The value is pinned to 0 (supply0) or 1
// (supply1) and the resolved strength is forced to supply on the driven side,
// overriding whatever the drivers contribute.
static void ResolveSupplyNet(Net& net, Arena& arena) {
  bool is_supply1 = net.type == NetType::kSupply1;
  if (is_supply1) {
    auto result = MakeLogic4Vec(arena, net.resolved->value.width);
    for (uint32_t w = 0; w < result.nwords; ++w) {
      result.words[w] = {~uint64_t{0}, 0};
    }
    net.resolved->value = result;
  } else {
    net.resolved->value = MakeLogic4VecVal(arena, net.resolved->value.width, 0);
  }
  net.resolved_strength = NetStrength{};
  Strength& hi =
      is_supply1 ? net.resolved_strength.s1_hi : net.resolved_strength.s0_hi;
  Strength& lo =
      is_supply1 ? net.resolved_strength.s1_lo : net.resolved_strength.s0_lo;
  hi = Strength::kSupply;
  lo = Strength::kSupply;
  net.resolved->NotifyWatchers();
}

// §28.15.2: once every driver goes to high impedance the trireg enters the
// charge storage state, retaining its last value. The drive resulting from
// that retained value carries the trireg's charge strength -- one of large,
// medium, or small, medium by default. Reflect that charge strength on the
// resolved drive (on the side matching the held value) so the stored charge
// competes with other sources at the correct level.
static void ResolveTriregCharge(Net& net, Scheduler* sched) {
  net.resolved_strength = NetStrength{};
  if (net.resolved->value.nwords > 0) {
    bool unknown = (net.resolved->value.words[0].bval & 1ull) != 0;
    bool high = (net.resolved->value.words[0].aval & 1ull) != 0;
    if (unknown || !high) {
      net.resolved_strength.s0_hi = net.charge_strength;
      net.resolved_strength.s0_lo = net.charge_strength;
    }
    if (unknown || high) {
      net.resolved_strength.s1_hi = net.charge_strength;
      net.resolved_strength.s1_lo = net.charge_strength;
    }
  }
  if (net.decay_ticks > 0 && sched != nullptr) {
    ScheduleDecay(net, sched);
  }
  net.resolved->NotifyWatchers();
}

static bool ResolveSpecialNet(Net& net, Arena& arena, Scheduler* sched) {
  if (net.type == NetType::kSupply0 || net.type == NetType::kSupply1) {
    ResolveSupplyNet(net, arena);
    return true;
  }
  if (net.type == NetType::kTrireg && AllDriversZ(net.drivers)) {
    ResolveTriregCharge(net, sched);
    return true;
  }
  if (ResolveTriPullDefault(net, arena)) return true;
  return false;
}

bool Net::InCapacitiveState() const {
  return type == NetType::kTrireg && AllDriversZ(drivers);
}

// §6.6.5: a tri0 (tri1) net is equivalent to a wire carrying a continuous 0 (1)
// of pull strength. When actual drivers are present, that implicit source
// combines with them in the normal strength resolution rather than merely
// filling the bits they leave floating: being pull strength, it overrides any
// real driver weaker than pull, ties an equal-strength pull driver into a
// conflict, and yields to strong/supply drivers. Materialize it as an extra
// driver appended to local copies of the driver/strength lists so the shared
// strength-resolution machinery applies it uniformly.
static void AppendTriPullDriver(std::vector<Logic4Vec>& drivers,
                                std::vector<DriverStrength>& strengths,
                                NetType type, uint32_t width, Arena& arena) {
  if (type != NetType::kTri0 && type != NetType::kTri1) return;
  auto pull = MakeLogic4Vec(arena, width);
  FillConstBit(pull, type == NetType::kTri1);
  drivers.push_back(pull);
  strengths.push_back(DriverStrength{Strength::kPull, Strength::kPull});
}

static void ResolveStrengthDriven(Net& net, Arena& arena) {
  std::vector<Logic4Vec> drivers = net.drivers;
  std::vector<DriverStrength> strengths = net.driver_strengths;
  AppendTriPullDriver(drivers, strengths, net.type, net.resolved->value.width,
                      arena);

  auto result = MakeLogic4Vec(arena, net.resolved->value.width);
  for (uint32_t b = 0; b < result.width; ++b) {
    ResolveStrengthBit(drivers, strengths, result, b, net.type);
  }
  FixupTriPull(result, net.type);
  net.resolved->value = result;
  ComputeSingleBitStrength(drivers, strengths, net.resolved_strength, net.type);
  net.resolved->NotifyWatchers();
}

static Logic4Vec CombineAllDrivers(const std::vector<Logic4Vec>& drivers,
                                   Arena& arena, NetType type) {
  Logic4Vec result = drivers[0];
  for (size_t i = 1; i < drivers.size(); ++i) {
    auto combined = MakeLogic4Vec(arena, result.width);
    for (uint32_t w = 0; w < result.nwords; ++w) {
      combined.words[w] =
          ResolveWord(result.words[w], drivers[i].words[w], type);
    }
    result = combined;
  }
  return result;
}

void Net::Resolve(Arena& arena, Scheduler* sched) {
  if (!resolved) return;

  if (resolved->is_forced) return;

  bool needs_resolution_when_undriven =
      is_user_nettype || type == NetType::kTri0 || type == NetType::kTri1;
  if (drivers.empty() && !needs_resolution_when_undriven) return;

  if (type == NetType::kTrireg && !AllDriversZ(drivers)) {
    ++decay_generation;
  }

  if (ResolveSpecialNet(*this, arena, sched)) return;

  if (!is_user_nettype && !driver_strengths.empty()) {
    ResolveStrengthDriven(*this, arena);
    return;
  }

  if (drivers.size() == 1) {
    resolved->value = drivers[0];
    FixupTriPull(resolved->value, type);
    resolved->NotifyWatchers();
    return;
  }

  Logic4Vec result = CombineAllDrivers(drivers, arena, type);
  FixupTriPull(result, type);
  resolved->value = result;
  resolved->NotifyWatchers();
}

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
    b.charge_strength = a.charge_strength;
    b.resolved->NotifyWatchers();
  } else if (sb > sa) {
    a.resolved->value = b.resolved->value;
    a.charge_strength = b.charge_strength;
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

bool ValidateNettypeDataKind(NettypeDataKind kind) {
  switch (kind) {
    case NettypeDataKind::k4StateIntegral:
    case NettypeDataKind::k2StateIntegral:
    case NettypeDataKind::kReal:
    case NettypeDataKind::kShortreal:
    case NettypeDataKind::kFixedUnpackedArray:
      return true;
    case NettypeDataKind::kDynamicArray:
    case NettypeDataKind::kString:
    case NettypeDataKind::kClass:
      return false;
  }
  return false;
}

bool ResolveUserDefinedNet(Net& net, const UserNettype& nettype, Arena& arena) {
  // With a resolution function the whole driver set is handed to the function,
  // which computes the single atomic value of the net. Without one the net is
  // left at its existing value (an undriven nettype net is unknown).
  if (nettype.resolution) {
    Logic4Vec result = nettype.resolution(arena, net.drivers);
    net.resolved->value = result;
  } else if (net.drivers.empty() && net.resolved) {
    // §6.6.7/§6.7.3: a logic net of an unresolved user-defined nettype with no
    // drivers takes the data type's default value, which for a 4-state type is
    // x (not z and not 0).
    SetAllX(net.resolved->value);
  }
  return true;
}

bool CheckUnresolvedMultipleDrivers(const Net& net, const UserNettype& nt) {
  return !nt.resolution && net.drivers.size() > 1;
}

// The 4-state data types default to x; the 2-state, real, and shortreal types
// default to a zero bit pattern. §6.7.3 leans on these defaults via Table 6-7.
static bool DataTypeDefaultsToX(NettypeDataKind kind) {
  switch (kind) {
    case NettypeDataKind::k4StateIntegral:
    case NettypeDataKind::kFixedUnpackedArray:
      return true;
    case NettypeDataKind::k2StateIntegral:
    case NettypeDataKind::kReal:
    case NettypeDataKind::kShortreal:
    case NettypeDataKind::kDynamicArray:
    case NettypeDataKind::kString:
    case NettypeDataKind::kClass:
      return false;
  }
  return true;
}

static void SetAllZero(Logic4Vec& val) {
  for (uint32_t w = 0; w < val.nwords; ++w) {
    val.words[w] = {0, 0};
  }
}

static void SetBit(Logic4Vec& val, uint32_t bit, uint64_t aval, uint64_t bval) {
  uint32_t w = bit / 64;
  uint64_t mask = uint64_t{1} << (bit % 64);
  if (aval & 1) {
    val.words[w].aval |= mask;
  } else {
    val.words[w].aval &= ~mask;
  }
  if (bval & 1) {
    val.words[w].bval |= mask;
  } else {
    val.words[w].bval &= ~mask;
  }
}

bool InitializeUserDefinedNet(Net& net, const UserNettype& nettype,
                              Arena& arena) {
  if (!net.resolved) return false;

  // §6.7.3: the initial value is the data-type default and must be in place
  // before the guaranteed resolution call (and before any procedure starts).
  if (DataTypeDefaultsToX(nettype.data_kind)) {
    SetAllX(net.resolved->value);
  } else {
    SetAllZero(net.resolved->value);
  }

  // §6.7.3: a resolved nettype's resolution function is activated at least once
  // at time zero -- even for an undriven net, where it sees an empty driver
  // set.
  if (nettype.resolution) {
    net.resolved->value = nettype.resolution(arena, net.drivers);
  }
  return true;
}

Logic4Vec InitialStructNetValue(Arena& arena, uint32_t total_width,
                                const std::vector<StructMemberInit>& members) {
  Logic4Vec value = MakeLogic4Vec(arena, total_width);
  // §6.7.3: members with no initializer keep the 4-state data-type default (x).
  SetAllX(value);
  // §6.7.3: any initialization expression for a struct member is applied.
  for (const auto& m : members) {
    if (!m.has_initializer) continue;
    for (uint32_t b = 0; b < m.width; ++b) {
      uint32_t src = b / 64;
      uint64_t bitmask = uint64_t{1} << (b % 64);
      uint64_t a = (m.init_value.words[src].aval & bitmask) ? 1 : 0;
      uint64_t bv = (m.init_value.words[src].bval & bitmask) ? 1 : 0;
      SetBit(value, m.offset + b, a, bv);
    }
  }
  return value;
}

}  // namespace delta
