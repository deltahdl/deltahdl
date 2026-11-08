#include <algorithm>
#include <cstdint>
#include <vector>

#include "common/types.h"
#include "simulator/net.h"

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

NetStrength CombineAmbigWithUnambig(NetStrength ambig, uint8_t vu, uint8_t su) {
  NetStrength r;
  Strength amb_vu_lo = (vu == 0) ? ambig.s0_lo : ambig.s1_lo;
  Strength amb_vu_hi = (vu == 0) ? ambig.s0_hi : ambig.s1_hi;
  Strength amb_opp_hi = (vu == 0) ? ambig.s1_hi : ambig.s0_hi;

  Strength& vu_lo = (vu == 0) ? r.s0_lo : r.s1_lo;
  Strength& vu_hi = (vu == 0) ? r.s0_hi : r.s1_hi;
  Strength& opp_lo = (vu == 0) ? r.s1_lo : r.s0_lo;
  Strength& opp_hi = (vu == 0) ? r.s1_hi : r.s0_hi;

  auto s_su = static_cast<Strength>(su);
  vu_hi = std::max(s_su, amb_vu_hi);
  if (static_cast<uint8_t>(amb_opp_hi) > su) {
    opp_hi = amb_opp_hi;
    opp_lo = Strength::kHighz;
    vu_lo = Strength::kHighz;
    return r;
  }
  vu_lo = std::max(s_su, amb_vu_lo);
  return r;
}

}  // namespace delta
