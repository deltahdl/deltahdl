#pragma once

#include <algorithm>
#include <cstdint>

#include "model_val4.h"

// --- Local types for strength modeling (§28.11-§28.14) ---
enum class StrengthLevel : uint8_t {
  kHighz = 0,
  kSmall = 1,
  kMedium = 2,
  kWeak = 3,
  kLarge = 4,
  kPull = 5,
  kStrong = 6,
  kSupply = 7,
};

// A strength signal carries a value and a range of strength levels per side.
// Sides are independent: side 0 carries value-0 levels, side 1 carries value-1
// levels. Unambiguous signals occupy a single level on the value side and
// kHighz on the other; ambiguous signals occupy a range on one or both sides.
// The _lo fields are exposed so §28.12.3 results — which can have a non-kHighz
// lower bound after rule b) trims a side — are representable.
struct StrengthSignal {
  Val4 value = Val4::kZ;
  StrengthLevel strength0_hi = StrengthLevel::kHighz;
  StrengthLevel strength1_hi = StrengthLevel::kHighz;
  StrengthLevel strength0_lo = StrengthLevel::kHighz;
  StrengthLevel strength1_lo = StrengthLevel::kHighz;
};

enum class ModelWiredLogicKind : uint8_t { kNone, kAnd, kOr };

inline StrengthLevel MapStrengthKeyword(uint8_t keyword_index);

inline bool ValidateStrengthPair(StrengthLevel s0, StrengthLevel s1);

inline StrengthSignal CombineUnambiguous(StrengthSignal a, StrengthSignal b);

inline StrengthSignal CombineWithWiredLogic(StrengthSignal a, StrengthSignal b,
                                            ModelWiredLogicKind logic);

inline StrengthSignal CombineAmbiguous(StrengthSignal a, StrengthSignal b);

inline StrengthSignal CombineAmbiguousWithUnambiguous(StrengthSignal unambig,
                                                      StrengthSignal ambig);

inline StrengthLevel ModelReduceNonresistive(StrengthLevel input);

inline StrengthLevel ModelReduceResistive(StrengthLevel input);

// --- Implementations ---
// §28.11's Table 28-7, which gives a strength name a level. One function
// answers both halves of a strength specification because the table gives
// `supply0` and `supply1` the level 7, `strong0` and `strong1` the level 6, and
// so on down to `highz0` and `highz1` at 0: the suffix says which portion of
// the net value the strength belongs to and does not change the level.
//
// The index is a position in the drive_strength keyword list §28.11 writes out
// -- none, highz, weak, pull, strong, supply -- and not a strength level.
// Table 28-7 also carries large, medium and small, which are the charge storage
// strengths of §28.15.2 rather than drive strengths, and which §28.11's two
// lists do not admit.
inline StrengthLevel MapStrengthKeyword(uint8_t keyword_index) {
  switch (keyword_index) {
    case 0:
    case 1:
      return StrengthLevel::kHighz;
    case 2:
      return StrengthLevel::kWeak;
    case 3:
      return StrengthLevel::kPull;
    case 4:
      return StrengthLevel::kStrong;
    case 5:
      return StrengthLevel::kSupply;
    default:
      return StrengthLevel::kHighz;
  }
}

// §28.11: "The combinations (highz0, highz1) and (highz1, highz0) shall be
// considered illegal." Both spellings name one pair once the two keywords are
// read as levels, so the rule is that the two sides are not both kHighz. Every
// other pair of the two lists is legal, the clause ruling out these and no
// others.
inline bool ValidateStrengthPair(StrengthLevel s0, StrengthLevel s1) {
  return s0 != StrengthLevel::kHighz || s1 != StrengthLevel::kHighz;
}

inline StrengthSignal CombineUnambiguous(StrengthSignal a, StrengthSignal b) {
  // Effective strength is the maximum of the two strength fields,
  // since for an unambiguous signal one side is always highz.
  auto effective = [](const StrengthSignal& s) -> StrengthLevel {
    return std::max(s.strength0_hi, s.strength1_hi);
  };

  StrengthLevel eff_a = effective(a);
  StrengthLevel eff_b = effective(b);

  if (a.value == b.value) {
    // Like values: result has same value with the greater strength.
    StrengthSignal result;
    result.value = a.value;
    StrengthLevel max_str = std::max(eff_a, eff_b);
    if (a.value == Val4::kV0) {
      result.strength0_hi = max_str;
      result.strength1_hi = StrengthLevel::kHighz;
    } else {
      result.strength0_hi = StrengthLevel::kHighz;
      result.strength1_hi = max_str;
    }
    return result;
  }

  // Unlike values: stronger signal dominates.
  if (eff_a > eff_b) {
    return a;
  } else if (eff_b > eff_a) {
    return b;
  }

  // Equal strength, unlike values: produce x.
  StrengthSignal result;
  result.value = Val4::kX;
  result.strength0_hi = eff_a;
  result.strength1_hi = eff_a;
  return result;
}

// §28.12.4: the net types triand, wand, trior and wor "shall resolve conflicts
// when multiple drivers have the same strength", by "treating signals as inputs
// of logic functions". The result has "the same value as the result produced by
// an and gate" or "an or gate" with the two values as inputs, and "the strength
// of the result is the same as the strength of the combined signals".
//
// Three of the clause's cases this function answers wrongly, all recorded in
// issue #3423 and none of them asserted by
// test_simulator_subclause_28_12_04.cpp:
//
// An operand spanning more than one level is collapsed to one by the max below,
// so the union §28.12.4 asks for -- "all combinations of each of the strength
// levels in the first signal with each of the strength levels in the second
// signal" -- is never formed. Figure 28-25 is the counterexample: a value 0
// over levels 6 and 5 combined by or logic with a value 1 at level 5 leaves a
// value-1 component surviving, and this returns an unambiguous 0.
//
// An x operand is answered by the complement of the one case tested for, where
// an and gate gives x for `1 and x` and an or gate gives x for `0 or x`.
// WiredAnd and WiredOr (simulator/net.cpp) answer those correctly.
//
// ModelWiredLogicKind::kNone falls to the or arm, so a check that names no
// wired logic resolves a strong 0 against a strong 1 to a definite 1 where
// §28.12.2 makes it ambiguous. §28.12.4 names four net types and no such case,
// and WiredLogicKind (simulator/net.h) declares no kNone.
inline StrengthSignal CombineWithWiredLogic(StrengthSignal a, StrengthSignal b,
                                            ModelWiredLogicKind logic) {
  // For different strengths, the stronger signal dominates (same as
  // unambiguous combination). Wired logic only applies when two
  // same-strength opposite-value signals combine.
  auto effective = [](const StrengthSignal& s) -> StrengthLevel {
    return std::max(s.strength0_hi, s.strength1_hi);
  };

  StrengthLevel eff_a = effective(a);
  StrengthLevel eff_b = effective(b);

  // If same value or different strengths, defer to unambiguous rules
  // (like values merge, stronger dominates).
  if (a.value == b.value || eff_a != eff_b) {
    return CombineUnambiguous(a, b);
  }

  // Same strength, opposite values: apply wired logic.
  Val4 resolved = Val4::kX;
  if (logic == ModelWiredLogicKind::kAnd) {
    // AND: 1&0=0, 1&1=1, 0&0=0
    if (a.value == Val4::kV1 && b.value == Val4::kV1) {
      resolved = Val4::kV1;
    } else {
      resolved = Val4::kV0;
    }
  } else {
    // OR: 1|0=1, 0|0=0, 1|1=1
    if (a.value == Val4::kV0 && b.value == Val4::kV0) {
      resolved = Val4::kV0;
    } else {
      resolved = Val4::kV1;
    }
  }

  StrengthSignal result;
  result.value = resolved;
  if (resolved == Val4::kV0) {
    result.strength0_hi = eff_a;
    result.strength1_hi = StrengthLevel::kHighz;
  } else {
    result.strength0_hi = StrengthLevel::kHighz;
    result.strength1_hi = eff_a;
  }
  return result;
}

// §28.12.2: combining two ambiguous-strength signals yields an ambiguous
// signal whose strength range on each side of the scale covers both inputs.
// Widening the range is a max on each side, and values merge with x wherever
// the inputs disagree.
//
// The per-side lower bound is left at kHighz and is not computed, which is
// right only where both components already reach high impedance. §28.12.2's
// own figures show components that do not: Figure 28-12 draws a 651 signal
// spanning Pu1 to St1 and Figure 28-13 a 530 signal spanning We0 to Pu0. Two
// same-value components anchored above high impedance are the case the clause
// illustrates nowhere and this function answers wrongly; issue #3423 records
// it, and test_simulator_subclause_28_12_02.cpp asserts only the shapes
// §28.12.2 settles.
inline StrengthSignal CombineAmbiguous(StrengthSignal a, StrengthSignal b) {
  StrengthSignal result;
  result.strength0_hi = std::max(a.strength0_hi, b.strength0_hi);
  result.strength1_hi = std::max(a.strength1_hi, b.strength1_hi);
  result.value = (a.value == b.value) ? a.value : Val4::kX;
  return result;
}

// §28.12.3: rules a/b/c for combining a known-value, single-level unambig
// signal with one component of an ambiguous-strength signal.
//   a) ambig levels strictly above Su survive on their original side;
//   b) ambig levels at or below Su disappear (subject to c);
//   c) if a) and b) leave a gap on the !Vu side because the signals are of
//      opposite value, the gap is filled down to Su+1.
// The unambig signal contributes its single level Su on the Vu side. Per-side
// surviving ranges are merged with that contribution into [lo, hi] form.
inline StrengthSignal CombineAmbiguousWithUnambiguous(StrengthSignal unambig,
                                                      StrengthSignal ambig) {
  bool vu_is_0 = unambig.value == Val4::kV0;
  StrengthLevel s_u = vu_is_0 ? unambig.strength0_hi : unambig.strength1_hi;
  auto s_u_idx = static_cast<uint8_t>(s_u);

  // Split the ambiguous signal into its component on the unambiguous value side
  // (Vu) and the opposite value side (!Vu).
  // The opposite-side lower bound is not needed: rule c always fills the gap
  // down to Su+1 whenever any opposite-value level survives.
  StrengthLevel amb_vu_lo = vu_is_0 ? ambig.strength0_lo : ambig.strength1_lo;
  StrengthLevel amb_vu_hi = vu_is_0 ? ambig.strength0_hi : ambig.strength1_hi;
  StrengthLevel amb_op_hi = vu_is_0 ? ambig.strength1_hi : ambig.strength0_hi;

  // Vu side (§28.12.3 rules a/b, same value): the unambiguous level Su is
  // always driven, and two drivers of the same value resolve to the stronger
  // one, so the result spans [max(Su, ambig_lo), max(Su, ambig_hi)]. Rule c
  // never fills a same-value gap, which is exactly why the lower bound is
  // clamped up to Su rather than extended down to it.
  StrengthLevel vu_lo = static_cast<StrengthLevel>(
      std::max<uint8_t>(s_u_idx, static_cast<uint8_t>(amb_vu_lo)));
  StrengthLevel vu_hi = static_cast<StrengthLevel>(
      std::max<uint8_t>(s_u_idx, static_cast<uint8_t>(amb_vu_hi)));

  // Opposite side (§28.12.3 rules a/b/c, opposite value): only ambiguous levels
  // strictly greater than Su survive (rules a/b); when any survive, the signals
  // are of opposite value so rule c fills the gap down to Su+1.
  StrengthLevel op_lo = StrengthLevel::kHighz;
  StrengthLevel op_hi = StrengthLevel::kHighz;
  if (static_cast<uint8_t>(amb_op_hi) > s_u_idx) {
    op_hi = amb_op_hi;
    op_lo = static_cast<StrengthLevel>(s_u_idx + 1);
  }

  StrengthSignal result;
  if (vu_is_0) {
    result.strength0_lo = vu_lo;
    result.strength0_hi = vu_hi;
    result.strength1_lo = op_lo;
    result.strength1_hi = op_hi;
  } else {
    result.strength1_lo = vu_lo;
    result.strength1_hi = vu_hi;
    result.strength0_lo = op_lo;
    result.strength0_hi = op_hi;
  }

  // The unambiguous signal always anchors its known value, so the result keeps
  // that value unless opposite-value levels survive, in which case it is
  // ambiguous (x).
  result.value = (op_hi != StrengthLevel::kHighz) ? Val4::kX : unambig.value;
  return result;
}

// §28.13, modelled independently of ReduceNonresistive in src/common/types.h,
// which is the simulator's own and takes a Strength rather than a
// StrengthLevel. The two names were one until issue #3417, which is how this
// header read as covered by test_simulator_subclause_28_13.cpp when every call
// there reached the simulator's function and none reached this one.
inline StrengthLevel ModelReduceNonresistive(StrengthLevel input) {
  // supply → strong; all others unchanged.
  if (input == StrengthLevel::kSupply) {
    return StrengthLevel::kStrong;
  }
  return input;
}

// §28.14's Table 28-8, modelled independently of ReduceResistive in
// src/common/types.h for the reason ModelReduceNonresistive above is.
inline StrengthLevel ModelReduceResistive(StrengthLevel input) {
  // Per Table 28-8:
  //   supply → pull, strong → pull, pull → weak, large → medium,
  //   weak → medium, medium → small, small → small, highz → highz.
  switch (input) {
    case StrengthLevel::kSupply:
    case StrengthLevel::kStrong:
      return StrengthLevel::kPull;
    case StrengthLevel::kPull:
      return StrengthLevel::kWeak;
    case StrengthLevel::kLarge:
    case StrengthLevel::kWeak:
      return StrengthLevel::kMedium;
    case StrengthLevel::kMedium:
    case StrengthLevel::kSmall:
      return StrengthLevel::kSmall;
    default:
      return StrengthLevel::kHighz;
  }
}
