#include "simulation/net.h"

#include "common/arena.h"
#include "simulation/scheduler.h"
#include "simulation/variable.h"

namespace delta {

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

static void ResolveStrengthBit(const std::vector<Logic4Vec>& drivers,
                               const std::vector<DriverStrength>& strengths,
                               Logic4Vec& result, uint32_t bit) {
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
      conflict = true;
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

// §6.6.6/§6.6.4: Handle supply nets and trireg charge retention.
// Returns true if the net type was handled (caller should return early).
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
  return false;
}

// --- Net::Resolve ---

bool Net::InCapacitiveState() const {
  return type == NetType::kTrireg && AllDriversZ(drivers);
}

void Net::Resolve(Arena& arena, Scheduler* sched) {
  if (!resolved || drivers.empty()) return;

  // Cancel pending decay when trireg exits capacitive state.
  if (type == NetType::kTrireg && !AllDriversZ(drivers)) {
    ++decay_generation;
  }

  if (ResolveSpecialNet(*this, arena, sched)) return;

  // Strength-aware path.
  if (!driver_strengths.empty()) {
    auto result = MakeLogic4Vec(arena, resolved->value.width);
    for (uint32_t b = 0; b < result.width; ++b) {
      ResolveStrengthBit(drivers, driver_strengths, result, b);
    }
    FixupTriPull(result, type);
    resolved->value = result;
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
    b.resolved->NotifyWatchers();
  } else if (sb > sa) {
    a.resolved->value = b.resolved->value;
    a.resolved->NotifyWatchers();
  } else if (!ValuesEqual(a.resolved->value, b.resolved->value)) {
    SetAllX(a.resolved->value);
    SetAllX(b.resolved->value);
    a.resolved->NotifyWatchers();
    b.resolved->NotifyWatchers();
  }
}

}  // namespace delta
