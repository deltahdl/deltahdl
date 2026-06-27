#pragma once

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

inline StrengthLevel MapStrengthKeyword0(uint8_t keyword_index);

inline StrengthLevel MapStrengthKeyword1(uint8_t keyword_index);

inline bool ValidateStrengthPair(StrengthLevel s0, StrengthLevel s1);

inline StrengthSignal CombineUnambiguous(StrengthSignal a, StrengthSignal b);

inline StrengthSignal CombineWithWiredLogic(StrengthSignal a, StrengthSignal b,
                                            ModelWiredLogicKind logic);

inline StrengthSignal CombineAmbiguous(StrengthSignal a, StrengthSignal b);

inline StrengthSignal CombineAmbiguousWithUnambiguous(StrengthSignal unambig,
                                                      StrengthSignal ambig);

inline StrengthLevel ReduceNonresistive(StrengthLevel input);

inline StrengthLevel ReduceResistive(StrengthLevel input);

// --- Implementations ---
inline StrengthLevel MapStrengthKeyword0(uint8_t keyword_index) {
  // 0=none, 1=highz, 2=weak, 3=pull, 4=strong, 5=supply
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

inline StrengthLevel MapStrengthKeyword1(uint8_t keyword_index) {
  // 0=none, 1=highz, 2=weak, 3=pull, 4=strong, 5=supply
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

inline bool ValidateStrengthPair(StrengthLevel s0, StrengthLevel s1) {
  // Both highz is illegal; all other combinations are legal.
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
// In the hi-only range encoding used here — the per-side lower bound is
// implicitly kHighz — widening the range is a max on each side. Values merge
// with x wherever the inputs disagree, otherwise the shared value carries
// through.
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
  uint8_t s_u_idx = static_cast<uint8_t>(s_u);

  // Split the ambiguous signal into its component on the unambiguous value side
  // (Vu) and the opposite value side (!Vu).
  StrengthLevel amb_vu_lo = vu_is_0 ? ambig.strength0_lo : ambig.strength1_lo;
  StrengthLevel amb_vu_hi = vu_is_0 ? ambig.strength0_hi : ambig.strength1_hi;
  StrengthLevel amb_op_lo = vu_is_0 ? ambig.strength1_lo : ambig.strength0_lo;
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

inline StrengthLevel ReduceNonresistive(StrengthLevel input) {
  // supply → strong; all others unchanged.
  if (input == StrengthLevel::kSupply) {
    return StrengthLevel::kStrong;
  }
  return input;
}

inline StrengthLevel ReduceResistive(StrengthLevel input) {
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
