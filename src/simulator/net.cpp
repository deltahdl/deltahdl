#include "simulator/net.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <tuple>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/contassign_delay.h"
#include "simulator/net_bit_outcomes.h"
#include "simulator/net_trireg.h"
#include "simulator/nettype_resolution.h"
#include "simulator/scheduler.h"
#include "simulator/switch_network.h"
#include "simulator/variable.h"

namespace delta {

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
  if (b && a) return {2};
  return {3};
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
  } else if (val == 2) {
    vec.words[word].aval |= mask;
    vec.words[word].bval |= mask;
  } else {
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

struct UnambigSignal {
  uint8_t vu;
  uint8_t su;
};

static std::vector<UnambigSignal> FindWeakerUnambig(
    const std::vector<Logic4Vec>& drivers,
    const std::vector<DriverStrength>& strengths, uint8_t max_str,
    uint32_t bit) {
  std::vector<UnambigSignal> weaker;
  for (size_t d = 0; d < drivers.size(); ++d) {
    uint8_t val = GetBitVal(drivers[d], bit).val;
    if (val > 1) continue;
    uint8_t str = EffectiveStrength(val, strengths[d]);
    if (str == 0 || str >= max_str) continue;
    weaker.push_back({val, str});
  }
  std::sort(weaker.begin(), weaker.end(),
            [](const UnambigSignal& a, const UnambigSignal& b) {
              return a.su > b.su;
            });
  return weaker;
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

static MaxTracker FoldDriversForBit(
    const std::vector<Logic4Vec>& drivers,
    const std::vector<DriverStrength>& strengths, NetType net_type,
    uint32_t bit) {
  MaxTracker m;
  for (size_t d = 0; d < drivers.size(); ++d) {
    uint8_t val = GetBitVal(drivers[d], bit).val;
    if (val == 3) continue;
    uint8_t str = EffectiveStrength(val, strengths[d]);
    if (str == 0) continue;
    FoldDriverIntoMax(val, str, net_type, m);
  }
  return m;
}

static void CombineWeakerUnambigInto(
    NetStrength& out, const std::vector<Logic4Vec>& drivers,
    const std::vector<DriverStrength>& strengths, uint8_t max_str,
    uint32_t bit) {
  for (const UnambigSignal& u :
       FindWeakerUnambig(drivers, strengths, max_str, bit)) {
    out = CombineAmbigWithUnambig(out, u.vu, u.su);
  }
}

static NetStrength UnknownDriverSignal(DriverStrength ds) {
  NetStrength one;
  bool drives0 = ds.s0 != Strength::kHighz;
  bool drives1 = ds.s1 != Strength::kHighz;
  if (drives0 && drives1) {
    one.s0_hi = one.s0_lo = ds.s0;
    one.s1_hi = one.s1_lo = ds.s1;
    return one;
  }
  if (drives0) {
    one.s0_hi = ds.s0;
    one.s0_lo = Strength::kHighz;
  }
  if (drives1) {
    one.s1_hi = ds.s1;
    one.s1_lo = Strength::kHighz;
  }
  return one;
}

static void UnknownValueStrength(const std::vector<Logic4Vec>& drivers,
                                 const std::vector<DriverStrength>& strengths,
                                 uint32_t bit, NetStrength& out) {
  bool combined_one = false;
  for (size_t d = 0; d < drivers.size(); ++d) {
    if (GetBitVal(drivers[d], bit).val != 2) continue;
    if (EffectiveStrength(2, strengths[d]) == 0) continue;
    NetStrength one = UnknownDriverSignal(strengths[d]);
    out = combined_one ? CombineAmbiguousStrength(out, one) : one;
    combined_one = true;
  }
}

static void ComputeSingleBitStrength(
    const std::vector<Logic4Vec>& drivers,
    const std::vector<DriverStrength>& strengths, NetStrength& out,
    NetType net_type, uint32_t bit) {
  MaxTracker m = FoldDriversForBit(drivers, strengths, net_type, bit);
  out = NetStrength{};
  if (m.val == 3) return;
  auto s = static_cast<Strength>(m.str);
  if (m.conflict) {
    out.s0_hi = s;
    out.s1_hi = s;
    CombineWeakerUnambigInto(out, drivers, strengths, m.str, bit);
    return;
  }
  if (m.val == 0) {
    out.s0_hi = out.s0_lo = s;
    return;
  }
  if (m.val == 1) {
    out.s1_hi = out.s1_lo = s;
    return;
  }
  UnknownValueStrength(drivers, strengths, bit, out);
  if (out.IsAmbiguous()) {
    CombineWeakerUnambigInto(out, drivers, strengths, m.str, bit);
  }
}

static void ResolveStrengthBit(const std::vector<Logic4Vec>& drivers,
                               const std::vector<DriverStrength>& strengths,
                               Logic4Vec& result, uint32_t bit,
                               NetType net_type) {
  MaxTracker m;
  for (size_t d = 0; d < drivers.size(); ++d) {
    uint8_t val = GetBitVal(drivers[d], bit).val;
    if (val == 3) continue;
    uint8_t str = EffectiveStrength(val, strengths[d]);
    if (str == 0) continue;
    FoldDriverIntoMax(val, str, net_type, m);
  }
  SetBit(result, bit, m.conflict ? 2 : m.val);
}

static bool AllDriversZ(const std::vector<Logic4Vec>& drivers) {
  for (const auto& drv : drivers) {
    for (uint32_t w = 0; w < drv.nwords; ++w) {
      uint32_t bits_in_word = drv.width - w * 64;
      uint64_t mask =
          bits_in_word >= 64 ? ~uint64_t{0} : (uint64_t{1} << bits_in_word) - 1;
      if ((drv.words[w].bval & mask) != mask) return false;
      if ((drv.words[w].aval & mask) != 0) return false;
    }
  }
  return true;
}

static bool AllSourcesZ(const Net& net) {
  return AllDriversZ(net.drivers) && AllDriversZ(net.switch_drivers);
}

static void SetAllX(Logic4Vec& val) {
  for (uint32_t w = 0; w < val.nwords; ++w) {
    val.words[w] = {~uint64_t{0}, ~uint64_t{0}};
  }
}

static bool ResolveTriPullDefault(Net& net, Arena& arena) {
  if (net.type != NetType::kTri0 && net.type != NetType::kTri1) return false;
  if (!AllSourcesZ(net)) return false;

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

static void ResolveSupplyNet(Net& net, Arena& arena) {
  bool is_supply1 = net.type == NetType::kSupply1;
  if (is_supply1) {
    auto result = MakeLogic4Vec(arena, net.resolved->value.width);
    FillConstBit(result, true);
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

static void WidenSide(Strength& hi, Strength& lo, Strength bit_hi,
                      Strength bit_lo) {
  if (bit_hi == Strength::kHighz) return;
  if (hi == Strength::kHighz) {
    hi = bit_hi;
    lo = bit_lo;
    return;
  }
  if (bit_hi > hi) hi = bit_hi;
  if (bit_lo < lo) lo = bit_lo;
}

static void WidenNetStrengthOverBit(NetStrength& net, const NetStrength& bit) {
  WidenSide(net.s0_hi, net.s0_lo, bit.s0_hi, bit.s0_lo);
  WidenSide(net.s1_hi, net.s1_lo, bit.s1_hi, bit.s1_lo);
}

static bool ResolveSpecialNet(Net& net, Arena& arena) {
  if ((net.type == NetType::kSupply0 || net.type == NetType::kSupply1) &&
      AllSourcesZ(net)) {
    ResolveSupplyNet(net, arena);
    return true;
  }
  if (ResolveTriPullDefault(net, arena)) return true;
  return false;
}

bool Net::InCapacitiveState() const {
  return type == NetType::kTrireg && AllSourcesZ(*this);
}

static void AppendImplicitNetSource(std::vector<Logic4Vec>& drivers,
                                    std::vector<DriverStrength>& strengths,
                                    NetType type, uint32_t width,
                                    Arena& arena) {
  bool supply = type == NetType::kSupply0 || type == NetType::kSupply1;
  if (type != NetType::kTri0 && type != NetType::kTri1 && !supply) return;
  auto source = MakeLogic4Vec(arena, width);
  FillConstBit(source, type == NetType::kTri1 || type == NetType::kSupply1);
  drivers.push_back(source);
  Strength level = supply ? Strength::kSupply : Strength::kPull;
  strengths.push_back(DriverStrength{level, level});
}

static void ResolveStrengthDriven(Net& net, Arena& arena,
                                  const Logic4Vec* charge = nullptr) {
  std::vector<Logic4Vec> drivers = net.drivers;
  std::vector<DriverStrength> strengths = net.driver_strengths;
  strengths.resize(drivers.size());
  drivers.insert(drivers.end(), net.switch_drivers.begin(),
                 net.switch_drivers.end());
  strengths.insert(strengths.end(), net.switch_strengths.begin(),
                   net.switch_strengths.end());
  if (charge != nullptr) {
    drivers.push_back(*charge);
    strengths.push_back({net.charge_strength, net.charge_strength});
  }
  AppendImplicitNetSource(drivers, strengths, net.type,
                          net.resolved->value.width, arena);

  auto result = MakeLogic4Vec(arena, net.resolved->value.width);
  net.resolved_strength = NetStrength{};
  for (uint32_t b = 0; b < result.width; ++b) {
    NetStrength bit_strength;
    if (AnyDriverUnknownAt(drivers, b) ||
        AnyDriverRangedAt(drivers, strengths, b)) {
      SetBit(result, b,
             ResolveBitOverDriverStates(drivers, strengths, net.type, b,
                                        bit_strength));
    } else {
      ResolveStrengthBit(drivers, strengths, result, b, net.type);
      ComputeSingleBitStrength(drivers, strengths, bit_strength, net.type, b);
    }
    net.bit_strengths.push_back(bit_strength);
    WidenNetStrengthOverBit(net.resolved_strength, bit_strength);
  }
  FixupTriPull(result, net.type);
  net.resolved->value = result;
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

static void ResolveForcedStrength(Net& net) {
  std::vector<Logic4Vec> drivers{net.resolved->value};
  std::vector<DriverStrength> strengths{{Strength::kStrong, Strength::kStrong}};
  net.resolved_strength = NetStrength{};
  for (uint32_t b = 0; b < net.resolved->value.width; ++b) {
    NetStrength bit_strength;
    ComputeSingleBitStrength(drivers, strengths, bit_strength, net.type, b);
    net.bit_strengths.push_back(bit_strength);
    WidenNetStrengthOverBit(net.resolved_strength, bit_strength);
  }
}

static void ApplyPartialForcedValue(Net& net, Arena& arena) {
  for (const auto& part : net.resolved->held_parts) {
    const auto& window = part.window;
    DepositBitField(net.resolved->value, window.dst_lo,
                    ExtractBitField(arena, net.resolved->forced_value,
                                    window.dst_lo, window.dst_width),
                    window.dst_width);
  }
}

static void ApplyPartialForcedStrength(Net& net) {
  if (net.bit_strengths.empty()) return;
  std::vector<Logic4Vec> drivers{net.resolved->value};
  std::vector<DriverStrength> strengths{{Strength::kStrong, Strength::kStrong}};
  net.resolved_strength = NetStrength{};
  for (uint32_t b = 0; b < net.bit_strengths.size(); ++b) {
    if (net.resolved->BitIsForced(b)) {
      NetStrength bit_strength;
      ComputeSingleBitStrength(drivers, strengths, bit_strength, net.type, b);
      net.bit_strengths[b] = bit_strength;
    }
    WidenNetStrengthOverBit(net.resolved_strength, net.bit_strengths[b]);
  }
}

NetStrength Net::BitStrength(uint32_t bit) const {
  if (bit < bit_strengths.size()) return bit_strengths[bit];
  return resolved_strength;
}

static void ResolveFromDrivers(Net& net, Arena& arena, Scheduler* sched);

static void ResolveNet(Net& net, Arena& arena, Scheduler* sched);

static bool SameNetStrength(const NetStrength& a, const NetStrength& b) {
  return std::tie(a.s0_hi, a.s0_lo, a.s1_hi, a.s1_lo) ==
         std::tie(b.s0_hi, b.s0_lo, b.s1_hi, b.s1_lo);
}

static bool ValuesEqual(const Logic4Vec& a, const Logic4Vec& b) {
  uint32_t n = (a.nwords < b.nwords) ? a.nwords : b.nwords;
  for (uint32_t w = 0; w < n; ++w) {
    if (a.words[w].aval != b.words[w].aval) return false;
    if (a.words[w].bval != b.words[w].bval) return false;
  }
  return true;
}

static void ResolveAfterNetDelay(Net& net, const ContAssignDelays& delays,
                                 Arena& arena, Scheduler* sched) {
  Variable* shown = net.resolved;
  Variable scratch;
  scratch.value = ExtractBitField(arena, shown->value, 0, shown->value.width);
  NetStrength shown_strength = net.resolved_strength;
  std::vector<NetStrength> shown_bits = net.bit_strengths;
  net.resolved = &scratch;
  ResolveNet(net, arena, sched);
  net.resolved = shown;
  Logic4Vec target = scratch.value;
  NetStrength target_strength = net.resolved_strength;
  std::vector<NetStrength> target_bits = net.bit_strengths;
  net.resolved_strength = shown_strength;
  net.bit_strengths = shown_bits;
  if (net.pending_value && ValuesEqual(*net.pending_value, target)) return;
  ++net.delay_generation;
  net.pending_value.reset();
  if (ValuesEqual(shown->value, target)) {
    net.resolved_strength = target_strength;
    net.bit_strengths = target_bits;
    return;
  }
  net.pending_value = target;
  uint64_t gen = net.delay_generation;
  auto* event = sched->GetEventPool().Acquire();
  event->kind = EventKind::kUpdate;
  event->callback = [&net, gen, target, target_strength, target_bits]() {
    if (net.delay_generation != gen) return;
    net.pending_value.reset();
    net.resolved->value = target;
    net.resolved_strength = target_strength;
    net.bit_strengths = target_bits;
    net.resolved->NotifyWatchers();
  };
  auto time = sched->CurrentTime();
  time.ticks +=
      SelectContAssignDelay(shown->value, target, delays, target.width);
  sched->ScheduleEvent(time, Region::kActive, event);
}

void Net::Resolve(Arena& arena, Scheduler* sched) {
  if (!resolved) return;
  NetStrength before = resolved_strength;
  if (delay && sched != nullptr && switch_links.empty() &&
      !resolved->is_forced) {
    ResolveAfterNetDelay(*this, *delay, arena, sched);
  } else {
    ++delay_generation;
    pending_value.reset();
    ResolveNet(*this, arena, sched);
  }
  if (!strength_watched || SameNetStrength(before, resolved_strength)) return;
  ++resolved->strength_generation;
  resolved->NotifyWatchers();
}

static void ResolveNet(Net& net, Arena& arena, Scheduler* sched) {
  if (!net.switch_links.empty() && ResolveSwitchGroup(net, arena, sched)) {
    return;
  }

  net.bit_strengths.clear();

  if (net.resolved->WholeIsForced()) {
    ResolveForcedStrength(net);
    return;
  }

  ResolveFromDrivers(net, arena, sched);
  if (net.resolved->is_forced) {
    ApplyPartialForcedValue(net, arena);
    ApplyPartialForcedStrength(net);
    net.resolved->NotifyWatchers();
  }
}

static void ResolveFromDrivers(Net& net, Arena& arena, Scheduler* sched) {
  bool needs_resolution_when_undriven =
      net.is_user_nettype || net.type == NetType::kTri0 ||
      net.type == NetType::kTri1 || net.type == NetType::kSupply0 ||
      net.type == NetType::kSupply1 || net.type == NetType::kTrireg;
  if (net.drivers.empty() && net.switch_drivers.empty() &&
      !needs_resolution_when_undriven) {
    return;
  }

  std::optional<Logic4Vec> charge;
  if (net.type == NetType::kTrireg)
    charge = SettleTriregCharge(net, arena, sched);

  if (ResolveSpecialNet(net, arena)) return;
  if (ResolveThroughNettypeFunction(net, arena)) return;

  bool supply = net.type == NetType::kSupply0 || net.type == NetType::kSupply1;
  if (!net.is_user_nettype &&
      (!net.driver_strengths.empty() || !net.switch_drivers.empty() || charge ||
       supply)) {
    ResolveStrengthDriven(net, arena, charge ? &*charge : nullptr);
    return;
  }

  std::vector<Logic4Vec> all = net.drivers;
  all.insert(all.end(), net.switch_drivers.begin(), net.switch_drivers.end());
  if (all.empty()) return;
  if (all.size() == 1) {
    net.resolved->value = all[0];
    FixupTriPull(net.resolved->value, net.type);
    net.resolved->NotifyWatchers();
    return;
  }

  Logic4Vec result = CombineAllDrivers(all, arena, net.type);
  FixupTriPull(result, net.type);
  net.resolved->value = result;
  net.resolved->NotifyWatchers();
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

}  // namespace delta
