#include "simulator/net_bit_outcomes.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "common/types.h"
#include "simulator/net.h"

namespace delta {

namespace {

struct BitState {
  uint8_t val = 3;
  uint8_t lvl = 0;
  bool exact = false;

  bool operator==(const BitState& other) const {
    return val == other.val && lvl == other.lvl && exact == other.exact;
  }
};

constexpr BitState kHighZ{3, 0};

uint8_t DriverBit(const Logic4Vec& v, uint32_t bit) {
  if (bit >= v.width) return 3;
  uint32_t word = bit / 64;
  uint64_t mask = uint64_t{1} << (bit % 64);
  bool aval = (v.words[word].aval & mask) != 0;
  bool bval = (v.words[word].bval & mask) != 0;
  if (!bval) return aval ? 1 : 0;
  return aval ? 2 : 3;
}

std::vector<BitState> KnownValueStates(uint8_t val, DriverStrength ds) {
  auto hi = static_cast<uint8_t>(val == 0 ? ds.s0 : ds.s1);
  auto lo = static_cast<uint8_t>(val == 0 ? ds.s0_lo : ds.s1_lo);
  if (hi == 0) return {kHighZ};
  if (lo == 0) return {BitState{val, hi}};
  return {BitState{val, hi}, BitState{val, lo}};
}

std::vector<BitState> DriverStates(uint8_t val, DriverStrength ds) {
  if (val < 2) return KnownValueStates(val, ds);
  auto s0 = static_cast<uint8_t>(ds.s0);
  auto s1 = static_cast<uint8_t>(ds.s1);
  if (val == 3) return {kHighZ};
  if (s0 != 0 && s0 == s1) return {BitState{2, s0, true}};
  std::vector<BitState> states;
  if (s0 != 0) states.push_back({0, s0});
  if (s1 != 0) states.push_back({1, s1});
  if (s0 == 0 || s1 == 0) states.push_back(kHighZ);
  return states;
}

uint8_t WiredAndValue(uint8_t a, uint8_t b) {
  if (a == 0 || b == 0) return 0;
  return (a == 1 && b == 1) ? 1 : 2;
}

uint8_t WiredOrValue(uint8_t a, uint8_t b) {
  if (a == 1 || b == 1) return 1;
  return (a == 0 && b == 0) ? 0 : 2;
}

BitState Combine(BitState a, BitState b, NetType type) {
  if (a.lvl == 0) return b;
  if (b.lvl == 0) return a;
  if (a.lvl != b.lvl) return a.lvl > b.lvl ? a : b;
  if (a.val == b.val) return {a.val, a.lvl, a.exact && b.exact};
  if (type == NetType::kWand || type == NetType::kTriand) {
    return {WiredAndValue(a.val, b.val), a.lvl};
  }
  if (type == NetType::kWor || type == NetType::kTrior) {
    return {WiredOrValue(a.val, b.val), a.lvl};
  }
  return {2, a.lvl};
}

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

struct SideLevels {
  uint8_t hi = 0;
  uint8_t lo = 8;

  void Take(uint8_t lvl) {
    hi = std::max(hi, lvl);
    lo = std::min(lo, lvl);
  }

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

bool AnyDriverRangedAt(const std::vector<Logic4Vec>& drivers,
                       const std::vector<DriverStrength>& strengths,
                       uint32_t bit) {
  for (size_t i = 0; i < drivers.size(); ++i) {
    uint8_t val = DriverBit(drivers[i], bit);
    Strength lo = val == 0 ? strengths[i].s0_lo : strengths[i].s1_lo;
    if (val < 2 && lo != Strength::kHighz) return true;
  }
  return false;
}

namespace {

struct ReachSummary {
  SideLevels side0;
  SideLevels side1;
  bool reaches_z = false;
  bool one_exact_x = false;
};

ReachSummary SummarizeReach(const std::vector<BitState>& reach) {
  ReachSummary sum;
  sum.one_exact_x = reach.size() == 1 && reach[0].exact;
  for (BitState s : reach) {
    if (s.lvl == 0) {
      sum.reaches_z = true;
      continue;
    }
    if (s.val != 1) sum.side0.Take(s.lvl);
    if (s.val != 0) sum.side1.Take(s.lvl);
  }
  return sum;
}

}  // namespace

uint8_t ResolveBitOverDriverStates(const std::vector<Logic4Vec>& drivers,
                                   const std::vector<DriverStrength>& strengths,
                                   NetType type, uint32_t bit,
                                   NetStrength& out) {
  const ReachSummary kSum =
      SummarizeReach(ReachableStates(drivers, strengths, type, bit));
  const SideLevels& side0 = kSum.side0;
  const SideLevels& side1 = kSum.side1;
  out = NetStrength{};
  if (side0.hi == 0 && side1.hi == 0) return 3;
  bool both = side0.hi != 0 && side1.hi != 0 && !kSum.one_exact_x;
  bool spread = both || kSum.reaches_z;
  side0.WriteTo(out.s0_hi, out.s0_lo, spread);
  side1.WriteTo(out.s1_hi, out.s1_lo, spread);
  if (spread || kSum.one_exact_x) return 2;
  return side0.hi != 0 ? 0 : 1;
}

}  // namespace delta
