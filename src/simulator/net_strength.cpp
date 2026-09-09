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

// §28.12.3 combines a signal of known value and unambiguous strength with each
// component of a signal of ambiguous strength, under three rules:
//
//   a) "The strength levels of the ambiguous strength signal that are greater
//      than the strength level of the unambiguous signal shall remain in the
//      result."
//   b) "The strength levels of the ambiguous strength signal that are smaller
//      than or equal to the strength level of the unambiguous signal shall
//      disappear from the result, subject to rule c)."
//   c) "If the operation of rule a) and rule b) results in a gap in strength
//      levels because the signals are of opposite value, the signals in the gap
//      shall be part of the result."
//
// What rule c's gap runs to is what the clause's words leave open and its
// figures settle. Figure 28-23 combines an ambiguous signal occupying the
// strength1 side with an unambiguous Pu0 and draws the result as one range
// running Pu0 through high impedance to St1, which its prose states as "a range
// defined by the greatest strength in the range of the ambiguous strength
// signal and by the strength level of the unambiguous strength signal". The gap
// is therefore bounded by the two surviving pieces rather than by the
// unambiguous level, and since those pieces sit on opposite sides of Figure
// 28-2's scale, filling it takes both sides down to high impedance.
//
// Where no opposite-value level survives there is no such gap, and the result
// is what rules a and b leave on the side the two signals share: Figure 28-20
// trims an ambiguous 0 range to [su, its own top], Figure 28-22 does the same
// on the strength1 side, and Figure 28-21 does it where the ambiguous signal's
// opposite-value component lies entirely at or below `su`. Two signals of one
// value resolve to the stronger of the two, which is what puts the lower bound
// at the greater of `su` and the ambiguous signal's own bound: a level above
// `su` settles the combination on its own, so `su` cannot appear below a range
// that begins above it.
//
// The consequence for the resolver is worth stating where it is read rather
// than where it is called: §28.12.2 gives an equal-strength opposite-value
// conflict "the strength levels of both signals and all the smaller strength
// levels", so every ambiguous signal Net::Resolve builds runs down to high
// impedance on both sides, and combining one with any weaker driver returns it
// unchanged. The function earns its keep on the one-sided ambiguous signal
// Figure 28-23 draws, which is what a three-state gate with an unknown control
// outputs (§28.12.2, Figure 28-6) and what this simulator does not build yet
// (#3468).
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
    // Rule a keeps the opposite-value levels above `su`, and rule c fills the
    // gap between them and the unambiguous signal's own level. That gap crosses
    // high impedance, so both sides reach it.
    opp_hi = amb_opp_hi;
    opp_lo = Strength::kHighz;
    vu_lo = Strength::kHighz;
    return r;
  }
  // Rule b took the whole opposite side, which leaves the two signals agreeing
  // on one value and no gap for rule c to fill.
  vu_lo = std::max(s_su, amb_vu_lo);
  return r;
}

}  // namespace delta
