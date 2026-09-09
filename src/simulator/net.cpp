#include "simulator/net.h"

#include <algorithm>

#include "common/arena.h"
#include "simulator/scheduler.h"
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

// §28.12.3's "signal of known value and unambiguous strength": one driver's
// value and the strength level it drives at, in the vocabulary
// CombineAmbigWithUnambig names them by.
struct UnambigSignal {
  uint8_t vu;
  uint8_t su;
};

// Every driver weaker than `max_str` that §28.12.3 has a combination to make
// with, strongest first. The clause combines a signal of known value and
// unambiguous strength with a component of the ambiguous strength signal, so a
// net with several weaker drivers has one such combination per driver rather
// than one for the strongest of them.
//
// Two kinds of driver are left out. One whose value is x or z is not a signal
// of known value, which is what the clause combines. One at the high-impedance
// level is not either: §21.2.1.4 states that the high-impedance strength cannot
// have a known logic value and that the only logic value allowed for that level
// is z. By §28.12.1 the stronger signal dominates it, so it combines to
// nothing, which is what leaving it out of the list says.
//
// The order is the strongest driver first, following §28.12.1's rule that the
// stronger signal dominates the weaker: the strongest weaker driver is the one
// that decides how far rules a and b move each bound, and every driver below it
// then combines against bounds already at or above its own level. Any other
// order gives the same result, because from a conflict range each combination
// only raises the two lower bounds to the level the driver puts there.
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

// The strongest driver of one bit, folded as §28.12.1 has the stronger signal
// dominate the weaker: the level, the value at that level, whether two values
// tie there, and the strength the winning driver carries.
static MaxTracker FoldDriversForBit(
    const std::vector<Logic4Vec>& drivers,
    const std::vector<DriverStrength>& strengths, NetType net_type,
    uint32_t bit) {
  MaxTracker m;
  for (size_t d = 0; d < drivers.size(); ++d) {
    uint8_t val = GetBitVal(drivers[d], bit).val;
    if (val == 3) continue;
    uint8_t str = EffectiveStrength(val, strengths[d]);
    // §21.2.1.4, as in ResolveStrengthBit above: a driver at the high-impedance
    // level drives nothing. FoldDriverIntoMax sets the conflict flag for one of
    // these on its own for the same reason, and the caller is saved from
    // reporting it only by the early return on an unset value below, which is a
    // guard on the answer rather than on the fold.
    if (str == 0) continue;
    FoldDriverIntoMax(val, str, net_type, m);
  }
  return m;
}

// §28.12.3: one combination per signal of known value and unambiguous strength
// weaker than the ambiguous one `out` holds, which is the clause's own shape --
// a range, and the drivers beneath it.
static void CombineWeakerUnambigInto(
    NetStrength& out, const std::vector<Logic4Vec>& drivers,
    const std::vector<DriverStrength>& strengths, uint8_t max_str,
    uint32_t bit) {
  for (const UnambigSignal& u :
       FindWeakerUnambig(drivers, strengths, max_str, bit)) {
    out = CombineAmbigWithUnambig(out, u.vu, u.su);
  }
}

// §28.12.2 classifies "signals with a value x" as having "strength levels
// consisting of subdivisions of both the strength1 and the strength0 parts of
// the scale of strengths", so a driver whose value is x stands on both sides of
// the scale, each at the level its own declaration drives that side at: it is
// the value that is unknown, not the strength. That is the case §21.2.1.4
// renders with a mnemonic -- "for the unknown value, a mnemonic is used when
// both the 0 and 1 strength components are at the same strength level".
//
// §28.6 Table 28-5 is the other shape, and it is spelt in the driver's own
// strength. A three-state gate with a control of x or z drives L or H -- "a
// result that has a value 0 or z" and "a value 1 or z" -- which §28.12.2's
// Figure 28-7 and Figure 28-8 draw as a range on one side of the scale running
// from the driving level down to high impedance, and nothing at all on the
// other. Such a driver spells x with the side it does not drive at the
// high-impedance level.
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

// §28.12.2: "The combination of two signals of ambiguous strength shall result
// in a signal of ambiguous strength. The resulting signal shall have a range of
// strength levels that includes the strength levels in its component signals."
// Figure 28-9 combines the PuH and the WeL two three-state gates with unknown
// controls drive and Figure 28-10 draws the result as one range from We0 across
// high impedance to Pu1, which §21.2.1.4 renders 35X. Every such driver joins
// the range whatever its level: §28.12.1's dominance is stated of a signal of
// unambiguous strength, and neither of those two dominates the other.
//
// A wired net reaches an unknown value through WiredAnd/WiredOr rather than by
// a driver spelling x, and the answer is the same either way, so the net type
// does not enter into it -- while it did, a strongly driven x on an ordinary
// wire filled neither side and was reported as nothing driving the net.
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
    // §28.12.3 makes one combination per signal of known value and unambiguous
    // strength, so every weaker driver is combined in turn. None of them moves
    // a bound here, and the reason is worth stating rather than discovering:
    // the range above runs from the conflict level down to high impedance on
    // both sides -- §28.12.2 gives such a conflict "the strength levels of both
    // signals and all the smaller strength levels" -- and §28.12.3's rule c
    // returns every level rule b takes out of it, the gap between the surviving
    // sides crossing high impedance (Figure 28-23). The combination is made
    // because the clause has it made, and it decides the one-sided range a
    // three-state gate with an unknown control drives (§28.6), which the arm
    // below builds.
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
    // §28.12.3 combines an ambiguous signal with each weaker signal of known
    // value and unambiguous strength, which is what Figure 28-23 draws for
    // exactly this shape: a one-sided range and a weaker driver of the other
    // value. An x driving both sides at one level is not ambiguous and nothing
    // weaker reaches it (§28.12.1).
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
    // §21.2.1.4: "The high-impedance strength cannot have a known logic value;
    // the only logic value allowed for this level is z." A driver at that level
    // therefore drives nothing whatever value it carries, and is passed over
    // the same way a driver already spelling z is. Folding it in instead made
    // it conflict with the nothing that had been seen so far -- MaxTracker::val
    // starts at 3, and a lone such driver matched the equal-strength test
    // against it, so a net one driver was holding at high impedance resolved to
    // x.
    if (str == 0) continue;
    FoldDriverIntoMax(val, str, net_type, m);
  }
  // §28.12.2: the value of a net two equally strong drivers disagree over is
  // unknown. A tracker that saw no driver keeps the unset value, which is the
  // z a net nothing drives holds.
  SetBit(result, bit, m.conflict ? 2 : m.val);
}

static bool AllDriversZ(const std::vector<Logic4Vec>& drivers) {
  // z = (aval=0, bval=1): a driver is all-z iff every bit set has bval set and
  // aval clear.
  //
  // The test is masked to the driver's own width. A Logic4Vec's final word
  // carries only `width % 64` significant bits and the bits above them are not
  // maintained, so comparing the whole word against ~0 asks about bits that
  // carry no value. That made this report false for every driver whose width is
  // not a multiple of 64 -- including every scalar one, where an all-z driver
  // has bval == 1 rather than ~0.
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
    // supply1 pins every bit to 1. Fill through the width-masked helper so the
    // unused high bits of the top word stay 0 -- an unmasked ~0 fill leaks into
    // the value read back through the full pipeline (e.g. a 1-bit supply1 net
    // reading back as all ones).
    auto result = MakeLogic4Vec(arena, net.resolved->value.width);
    FillConstBit(result, /*one=*/true);
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

// Widen one side of a net's reported strength to take in what one of its bits
// resolves to there.
//
// §28.12.2 has a signal's strength be a range of levels rather than one level
// where it is ambiguous, and that is what a net whose bits do not resolve alike
// reports: the range on each side spans every bit that drives that side. A bit
// leaving the side at highz drives nothing there and widens nothing, so a side
// no bit drives stays highz, and a net whose bits all resolve alike reports
// exactly what one of them does -- which is what a scalar net, the only width
// §21.2.1.4 gives %v, has always reported.
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

// §28.15.2: the charge one bit of a trireg holds, as the strength of a drive.
// The trireg's charge strength is declared once for the net -- "one of these
// three strengths: large, medium, or small" -- while the value it retains in
// the capacitive state is a value per bit (§6.6.4), so which side of the scale
// the charge appears on is what the bit decides. A bit holding 0 is charged
// low, one holding 1 is charged high, and one holding neither is charged on
// both sides, the same way §28.12.2 puts a signal of value x on "subdivisions
// of both the strength1 and the strength0 parts of the scale".
static NetStrength TriregBitCharge(const Logic4Vec& value, uint32_t bit,
                                   Strength charge) {
  NetStrength out;
  BitVal v = GetBitVal(value, bit);
  if (v.val != 1) {
    out.s0_hi = charge;
    out.s0_lo = charge;
  }
  if (v.val != 0) {
    out.s1_hi = charge;
    out.s1_lo = charge;
  }
  return out;
}

// §28.15.2: once every driver goes to high impedance the trireg enters the
// charge storage state, retaining its last value. The drive resulting from that
// retained value carries the trireg's charge strength -- one of large, medium,
// or small, medium by default. Reflect that charge strength on the resolved
// drive so the stored charge competes with other sources at the correct level.
//
// The value retained is per bit, and §28.12 resolves each bit of a net on its
// own, so each bit's charge is computed and then folded into the one pair the
// net reports. Reading bit 0 and letting it stand for the rest said of a
// `trireg [63:0]` holding 64'd1 that it was charged high and not low, when
// sixty-three of its bits were charged low (#3465).
static void ResolveTriregCharge(Net& net, Scheduler* sched) {
  net.resolved_strength = NetStrength{};
  for (uint32_t b = 0; b < net.resolved->value.width; ++b) {
    NetStrength bit_charge =
        TriregBitCharge(net.resolved->value, b, net.charge_strength);
    net.bit_strengths.push_back(bit_charge);
    WidenNetStrengthOverBit(net.resolved_strength, bit_charge);
  }
  // §28.16.2.1: the decay process ends when "the delay specified by charge
  // decay time elapses, and the trireg net makes a transition from 1 or 0 to
  // x", so a charge decay time of zero schedules that transition at the current
  // time rather than never. Reading the count alone left a `trireg #(0, 0, 0)`
  // holding its charge for the whole run, which is what §28.16.2.2 gives a
  // declaration writing no third delay instead.
  if (net.decays && sched != nullptr) {
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
  net.resolved_strength = NetStrength{};
  for (uint32_t b = 0; b < result.width; ++b) {
    ResolveStrengthBit(drivers, strengths, result, b, net.type);
    // §28.12 resolves each bit of a net on its own, and the strength of the
    // signal it resolves to is a property of that bit. A net reports one pair,
    // so each bit's contribution is folded into it rather than one bit being
    // taken to speak for the rest.
    NetStrength bit_strength;
    ComputeSingleBitStrength(drivers, strengths, bit_strength, net.type, b);
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

// §10.6.2: "A force procedural statement on a net shall override all drivers of
// the net -- gate outputs, module outputs, and continuous assignments -- until
// a release procedural statement is executed on the net." So while the force
// stands the net has one source and it is the force, and the strength it
// reports is that source's rather than the overridden drivers'.
//
// Which strength that is: §10.6 gives force no drive_strength syntax to carry
// one, and §10.3.4 defaults a continuous assignment that specifies none to
// (strong1, strong0). §21.7.4.3.2 counts a procedural continuous assignment
// among the drivers a port record reports, so there is something to report and
// the default is what it is. The forced value is folded through the same
// per-bit machinery an ordinary driver goes through, so a forced 0 lands on the
// 0 side, a forced 1 on the 1 side, a forced x on both (§28.12.2) and a forced
// z on neither.
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

// §10.6.2: a force on "a constant bit-select of a vector net, a constant
// part-select of a vector net" overrides the drivers of those bits and no
// others, so the resolution below runs as it always does and the forced bits
// are laid back over its answer. forced_value carries the whole object with
// those bits in place, which is where they are read from and where they go.
static void ApplyPartialForcedValue(Net& net, Arena& arena) {
  const auto& window = net.resolved->forced_window;
  DepositBitField(net.resolved->value, window.dst_lo,
                  ExtractBitField(arena, net.resolved->forced_value,
                                  window.dst_lo, window.dst_width),
                  window.dst_width);
}

// The strength of the bits a partial force holds, which §10.6.2 makes the
// force's rather than any driver's. The bits it does not hold keep the strength
// the driver resolution just gave them, and the net's own strength is widened
// back over the two kinds together. A resolution that recorded no per-bit
// strength at all is left alone: it answers every bit from resolved_strength,
// and there is no entry to correct.
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

// Resolves the net from its drivers, which is every rule but §10.6.2's force.
static void ResolveFromDrivers(Net& net, Arena& arena, Scheduler* sched);

void Net::Resolve(Arena& arena, Scheduler* sched) {
  if (!resolved) return;

  // Every resolution below either records one strength per bit or gives the
  // whole net one, so what a previous resolution recorded says nothing about
  // this one and is dropped before it runs.
  bit_strengths.clear();

  // §10.6.2: "A force procedural statement on a net shall override all drivers
  // of the net", and a force naming the whole net leaves no bit for a driver to
  // reach, so the drivers are not resolved at all. A force naming a select of
  // the net overrides the drivers of those bits alone: the rest of the net goes
  // on being driven, which is a resolution followed by the forced bits being
  // laid back over it. Reading the flag alone here dropped every driver of
  // every bit, so `assign bus = 8'h55;` stopped reaching bits 7:4 and 2:0 the
  // moment `force bus[3] = 1'b1;` ran.
  if (resolved->WholeIsForced()) {
    ResolveForcedStrength(*this);
    return;
  }

  ResolveFromDrivers(*this, arena, sched);
  if (resolved->is_forced) {
    ApplyPartialForcedValue(*this, arena);
    ApplyPartialForcedStrength(*this);
    resolved->NotifyWatchers();
  }
}

static void ResolveFromDrivers(Net& net, Arena& arena, Scheduler* sched) {
  // §28.15.3: a supply0/supply1 net models a constant ground/power connection,
  // so it carries value 0/1 at supply strength inherently -- like tri0/tri1, it
  // must resolve even with no driver connected rather than staying z.
  bool needs_resolution_when_undriven =
      net.is_user_nettype || net.type == NetType::kTri0 ||
      net.type == NetType::kTri1 || net.type == NetType::kSupply0 ||
      net.type == NetType::kSupply1;
  if (net.drivers.empty() && !needs_resolution_when_undriven) return;

  if (net.type == NetType::kTrireg && !AllDriversZ(net.drivers)) {
    ++net.decay_generation;
  }

  if (ResolveSpecialNet(net, arena, sched)) return;

  if (!net.is_user_nettype && !net.driver_strengths.empty()) {
    ResolveStrengthDriven(net, arena);
    return;
  }

  if (net.drivers.size() == 1) {
    net.resolved->value = net.drivers[0];
    FixupTriPull(net.resolved->value, net.type);
    net.resolved->NotifyWatchers();
    return;
  }

  Logic4Vec result = CombineAllDrivers(net.drivers, arena, net.type);
  FixupTriPull(result, net.type);
  net.resolved->value = result;
  net.resolved->NotifyWatchers();
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
