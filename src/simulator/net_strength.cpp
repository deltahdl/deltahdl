// The §28.12 strength algebra and the word-level net resolvers.
//
// §28.12.2 has a signal's strength be a range of levels rather than one level
// where it is ambiguous, and §28.12.3 and §28.12.4 say what combining two such
// signals gives: CombineAmbiguousStrength takes the per-side extremes of two
// ambiguous signals, CombineWiredLogicAmbiguous does the same combination for
// the wired-logic nets §28.12.4 excludes from that shortcut, and
// CombineAmbigWithUnambig applies §28.12.3's rules a, b and c to an ambiguous
// signal and a signal of known value and unambiguous strength. ResolveWireWord,
// ResolveWandWord and ResolveWorWord resolve a whole 64-bit word of two drivers
// at once, under the 4-state encoding of LRM Figure 38-8.
//
// The per-bit machinery that spends these -- the strength of one bit of a net,
// and the resolution of a net as a whole -- is in src/simulator/net.cpp.

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

// §28.12.3 rules a and b: the ambiguous levels above `su` remain in the result
// and those at or below it disappear. A side whose whole range sits at or below
// `su` disappears entirely, which is what leaving the outputs at their highz
// default says.
static void TrimAmbigSide(Strength a_lo, Strength a_hi, uint8_t su,
                          Strength& r_lo, Strength& r_hi) {
  if (static_cast<uint8_t>(a_hi) <= su) return;
  uint8_t lo_idx = std::max<uint8_t>(static_cast<uint8_t>(a_lo),
                                     static_cast<uint8_t>(su + 1));
  r_lo = static_cast<Strength>(lo_idx);
  r_hi = a_hi;
}

// §28.12.3 rule c: where rules a and b leave a gap in strength levels because
// the signals are of opposite value, the levels in the gap are part of the
// result. The gap runs from just above `su`, the strongest level rule b
// removed, up to the lowest level that survived, so filling it takes the lower
// bound back down to `su` + 1. A gap needs the unambiguous signal's own level
// to bound it from below, which `su_in_result` reports: where every level of
// the ambiguous signal is stronger than `su`, §28.12.1 has the stronger signal
// dominate, the unambiguous signal is in no part of the result, and the levels
// below the surviving ones lie under nothing rather than in a gap.
static void FillRuleCGap(Strength& r_lo, Strength r_hi, uint8_t su,
                         bool su_in_result) {
  if (r_hi == Strength::kHighz) return;
  if (!su_in_result) return;
  if (static_cast<uint8_t>(r_lo) <= su + 1) return;
  r_lo = static_cast<Strength>(su + 1);
}

NetStrength CombineAmbigWithUnambig(NetStrength ambig, uint8_t vu, uint8_t su) {
  NetStrength r;
  Strength amb_vu_lo = (vu == 0) ? ambig.s0_lo : ambig.s1_lo;
  Strength amb_vu_hi = (vu == 0) ? ambig.s0_hi : ambig.s1_hi;
  Strength amb_opp_lo = (vu == 0) ? ambig.s1_lo : ambig.s0_lo;
  Strength amb_opp_hi = (vu == 0) ? ambig.s1_hi : ambig.s0_hi;

  // The unambiguous signal's own level stands in the result exactly where the
  // ambiguous signal has a level at or below it: such a level resolves against
  // `su` to `su` itself, while §28.12.1 has an ambiguous signal every one of
  // whose levels is stronger dominate the unambiguous signal outright. This is
  // the same test the side of `vu` applies below, where it puts the lower bound
  // at the greater of `su` and the ambiguous signal's own bound.
  bool su_in_result = static_cast<uint8_t>(amb_vu_lo) <= su;

  Strength& opp_hi = (vu == 0) ? r.s1_hi : r.s0_hi;
  Strength& opp_lo = (vu == 0) ? r.s1_lo : r.s0_lo;
  TrimAmbigSide(amb_opp_lo, amb_opp_hi, su, opp_lo, opp_hi);
  FillRuleCGap(opp_lo, opp_hi, su, su_in_result);

  // §28.12.3 on the side of the unambiguous signal's own value: the two signals
  // agree there, so each level the ambiguous signal might have resolves against
  // `su` to whichever of the two is stronger, and the range of those results is
  // what the side contributes. A level at or below `su` therefore leaves the
  // result as rule b says while `su` itself stays, and a level above `su`
  // settles the combination on its own, which is why `su` cannot appear below
  // an ambiguous range that begins above it.
  auto s_su = static_cast<Strength>(su);
  Strength& vu_hi = (vu == 0) ? r.s0_hi : r.s1_hi;
  Strength& vu_lo = (vu == 0) ? r.s0_lo : r.s1_lo;
  vu_lo = std::max(s_su, amb_vu_lo);
  vu_hi = std::max(s_su, amb_vu_hi);
  return r;
}

}  // namespace delta
