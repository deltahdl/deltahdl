#include "simulator/net_bit_outcomes.h"

#include <algorithm>
#include <cstdint>
#include <vector>

#include "common/types.h"
#include "simulator/net.h"

namespace delta {

namespace {

// One state a bit can stand in: a value at a strength level, or high
// impedance at level 0. The value is 0 or 1, or x where two opposite values
// meet at one level (§28.12.2's "two signals of equal strength and opposite
// value"), which stands on both sides of the scale at that level.
struct BitState {
  uint8_t val = 3;
  uint8_t lvl = 0;

  bool operator==(const BitState& other) const {
    return val == other.val && lvl == other.lvl;
  }
};

constexpr BitState kHighZ{3, 0};

// The value one driver puts on bit `bit`, numbered 0, 1, 2 for x and 3 for z.
uint8_t DriverBit(const Logic4Vec& v, uint32_t bit) {
  if (bit >= v.width) return 3;
  uint32_t word = bit / 64;
  uint64_t mask = uint64_t{1} << (bit % 64);
  bool aval = (v.words[word].aval & mask) != 0;
  bool bval = (v.words[word].bval & mask) != 0;
  if (!bval) return aval ? 1 : 0;
  return aval ? 2 : 3;
}

// The states one driver can stand in: a known value at the level its strength
// gives that value, high impedance for a z or for a value driven at the
// high-impedance level (§21.2.1.4), and for an x the 0 and the 1 at the levels
// its two strengths give them -- with z besides where one of them is at the
// high-impedance level, which is the L or the H of §28.6 and §28.7.
std::vector<BitState> DriverStates(uint8_t val, DriverStrength ds) {
  auto s0 = static_cast<uint8_t>(ds.s0);
  auto s1 = static_cast<uint8_t>(ds.s1);
  if (val == 0) return {s0 != 0 ? BitState{0, s0} : kHighZ};
  if (val == 1) return {s1 != 0 ? BitState{1, s1} : kHighZ};
  if (val == 3) return {kHighZ};
  std::vector<BitState> states;
  if (s0 != 0) states.push_back({0, s0});
  if (s1 != 0) states.push_back({1, s1});
  if (s0 == 0 || s1 == 0) states.push_back(kHighZ);
  return states;
}

// §28.12.4 Table 6-3 and Table 6-4 on the values of two signals of equal
// strength, x standing for either value.
uint8_t WiredAndValue(uint8_t a, uint8_t b) {
  if (a == 0 || b == 0) return 0;
  return (a == 1 && b == 1) ? 1 : 2;
}

uint8_t WiredOrValue(uint8_t a, uint8_t b) {
  if (a == 1 || b == 1) return 1;
  return (a == 0 && b == 0) ? 0 : 2;
}

// Two states meeting on one bit: §28.12.1 has the stronger dominate, high
// impedance being the weakest of all, and at one level two opposite values are
// x on a wire (§28.12.2) and the logic function of a wired net (§28.12.4).
BitState Combine(BitState a, BitState b, NetType type) {
  if (a.lvl == 0) return b;
  if (b.lvl == 0) return a;
  if (a.lvl != b.lvl) return a.lvl > b.lvl ? a : b;
  if (a.val == b.val) return a;
  if (type == NetType::kWand || type == NetType::kTriand) {
    return {WiredAndValue(a.val, b.val), a.lvl};
  }
  if (type == NetType::kWor || type == NetType::kTrior) {
    return {WiredOrValue(a.val, b.val), a.lvl};
  }
  return {2, a.lvl};
}

// The states reachable once one more driver, able to stand in `states`, meets
// each state already reachable from `reach`, each kept once.
std::vector<BitState> FoldDriver(const std::vector<BitState>& reach,
                                 const std::vector<BitState>& states,
                                 NetType type) {
  std::vector<BitState> next;
  for (BitState from : reach) {
    for (BitState state : states) {
      BitState to = Combine(from, state, type);
      if (std::find(next.begin(), next.end(), to) == next.end()) {
        next.push_back(to);
      }
    }
  }
  return next;
}

// Every state the drivers together can leave the bit in. Each driver is
// folded in against each state already reachable, so the set never holds more
// than the handful of values and levels there are, however many drivers are
// ambiguous.
std::vector<BitState> ReachableStates(
    const std::vector<Logic4Vec>& drivers,
    const std::vector<DriverStrength>& strengths, NetType type, uint32_t bit) {
  std::vector<BitState> reach{kHighZ};
  for (size_t d = 0; d < drivers.size() && d < strengths.size(); ++d) {
    reach = FoldDriver(
        reach, DriverStates(DriverBit(drivers[d], bit), strengths[d]), type);
  }
  return reach;
}

// The levels one side of the scale is reached at, over the reachable states.
struct SideLevels {
  uint8_t hi = 0;
  uint8_t lo = 8;

  void Take(uint8_t lvl) {
    hi = std::max(hi, lvl);
    lo = std::min(lo, lvl);
  }

  // Writes the side into a net strength's two bounds for it, the low one at
  // high impedance where the range runs down through it.
  void WriteTo(Strength& out_hi, Strength& out_lo, bool to_highz) const {
    if (hi == 0) return;
    out_hi = static_cast<Strength>(hi);
    out_lo = to_highz ? Strength::kHighz : static_cast<Strength>(lo);
  }
};

}  // namespace

bool AnyDriverUnknownAt(const std::vector<Logic4Vec>& drivers, uint32_t bit) {
  return std::any_of(drivers.begin(), drivers.end(), [bit](const Logic4Vec& v) {
    return DriverBit(v, bit) == 2;
  });
}

// The range runs over every level a reachable state stands at, and where the
// states reach both sides of the scale, or reach high impedance, it runs down
// through high impedance as §28.12.2 draws such a range (Figure 28-5, Figure
// 28-10).
uint8_t ResolveBitOverDriverStates(const std::vector<Logic4Vec>& drivers,
                                   const std::vector<DriverStrength>& strengths,
                                   NetType type, uint32_t bit,
                                   NetStrength& out) {
  SideLevels side0;
  SideLevels side1;
  bool reaches_z = false;
  for (BitState s : ReachableStates(drivers, strengths, type, bit)) {
    if (s.lvl == 0) {
      reaches_z = true;
      continue;
    }
    if (s.val != 1) side0.Take(s.lvl);
    if (s.val != 0) side1.Take(s.lvl);
  }
  out = NetStrength{};
  if (side0.hi == 0 && side1.hi == 0) return 3;
  bool both = side0.hi != 0 && side1.hi != 0;
  side0.WriteTo(out.s0_hi, out.s0_lo, both || reaches_z);
  side1.WriteTo(out.s1_hi, out.s1_lo, both || reaches_z);
  if (both || reaches_z) return 2;
  return side0.hi != 0 ? 0 : 1;
}

}  // namespace delta
