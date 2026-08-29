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

// A strength signal as Figure 28-2 draws one: a span of the sixteen cells the
// strength scale holds, which are Su0 St0 Pu0 La0 We0 Me0 Sm0 HiZ0 on the
// strength0 side and HiZ1 Sm1 Me1 We1 La1 Pu1 St1 Su1 on the strength1 side.
//
// A side is occupied when its _hi is above kHighz, and it then occupies every
// level from its _lo up to its _hi. An unambiguous signal occupies one cell, so
// it is written with _lo equal to _hi on its value's side and kHighz on the
// other; a signal built with _lo left at kHighz occupies its side down to high
// impedance, which is what a switch network's output does and what §28.12.3's
// rules a) and b) trim. A signal occupying cells on both sides has the value x,
// one occupying neither has the value z, and `value` says which.
//
// Both _lo and _hi are read. CombineAmbiguous and CombineWithWiredLogic below
// take the extremes over these spans, which §28.12.2 states as "a range that
// includes the extremes of the signals and all the strengths between them";
// before issue #3423 the two functions read _hi alone and answered a signal
// anchored above high impedance, such as Figure 28-12's Pu1 to St1, as though
// it reached high impedance.
struct StrengthSignal {
  Val4 value = Val4::kZ;
  StrengthLevel strength0_hi = StrengthLevel::kHighz;
  StrengthLevel strength1_hi = StrengthLevel::kHighz;
  StrengthLevel strength0_lo = StrengthLevel::kHighz;
  StrengthLevel strength1_lo = StrengthLevel::kHighz;
};

// The two logic functions §28.12.4 resolves a wired net with. The clause names
// triand and wand for the first and trior and wor for the second, and no fifth
// case: a net that is not one of the four is resolved by §28.12.2 and never
// reaches CombineWithWiredLogic. WiredLogicKind (simulator/net.h) declares the
// same two enumerators for the same reason.
enum class ModelWiredLogicKind : uint8_t { kAnd, kOr };

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
  // Effective strength is the maximum of the two strength fields, since for an
  // unambiguous signal one side is always highz. The result is written with its
  // _lo equal to its _hi, an unambiguous signal occupying one cell of Figure
  // 28-2's scale, which is the encoding StrengthSignal above states.
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
      result.strength0_lo = max_str;
    } else {
      result.strength1_hi = max_str;
      result.strength1_lo = max_str;
    }
    return result;
  }

  // Unlike values: stronger signal dominates.
  if (eff_a > eff_b) {
    return a;
  } else if (eff_b > eff_a) {
    return b;
  }

  // Equal strength, unlike values: produce x. §28.12.1 gives the result that
  // one strength on each side, so it occupies one cell of each rather than a
  // range, and both _lo fields match their _hi.
  StrengthSignal result;
  result.value = Val4::kX;
  result.strength0_hi = eff_a;
  result.strength0_lo = eff_a;
  result.strength1_hi = eff_a;
  result.strength1_lo = eff_a;
  return result;
}

// A cell of Figure 28-2's scale, as a position running from Su0 at 0 to Su1 at
// 15. Ordering the sixteen cells on one line is what lets "all the strengths
// between them" be a span rather than two separate ranges: §28.12.2's own
// Figure 28-10 draws a range crossing from We0 through HiZ0 and HiZ1 to Pu1,
// which no per-side pair of levels expresses on its own.
inline int ScalePositionOf(StrengthLevel level, bool side_is_1) {
  int index = static_cast<int>(level);
  return side_is_1 ? 8 + index : 7 - index;
}

// The cells one signal occupies, as the closed span [lo, hi] of scale
// positions. `occupied` is false for a signal that occupies none, which is the
// z §28.12 leaves out of every combination.
struct ScaleSpan {
  bool occupied = false;
  int lo = 0;
  int hi = 0;
};

inline void ExtendSpan(ScaleSpan& span, int position) {
  if (!span.occupied) {
    span = ScaleSpan{true, position, position};
    return;
  }
  span.lo = std::min(span.lo, position);
  span.hi = std::max(span.hi, position);
}

inline ScaleSpan SpanOf(const StrengthSignal& s) {
  ScaleSpan span;
  if (s.strength0_hi != StrengthLevel::kHighz) {
    ExtendSpan(span, ScalePositionOf(s.strength0_hi, false));
    ExtendSpan(span, ScalePositionOf(s.strength0_lo, false));
  }
  if (s.strength1_hi != StrengthLevel::kHighz) {
    ExtendSpan(span, ScalePositionOf(s.strength1_lo, true));
    ExtendSpan(span, ScalePositionOf(s.strength1_hi, true));
  }
  return span;
}

// The signal a span of the scale stands for. A span reaching both sides holds
// cells of both values, which is the x §28.12.2 gives "because its range
// includes the values 1 and 0"; one reaching neither is z.
//
// A signal occupying HiZ0 alone, or HiZ1 alone, is the one thing StrengthSignal
// cannot say, a side being occupied only when its _hi is above kHighz. Nothing
// asks it to: SpanOf reads a side only when that side's _hi is above kHighz, so
// the spans it produces always reach a cell off positions 7 and 8, and a pair
// of such spans cannot resolve to position 7 or 8 alone. §28.12 combines no
// such signal either, high impedance being what a driver contributes when it
// drives nothing.
inline StrengthSignal SignalOfSpan(const ScaleSpan& span) {
  StrengthSignal result;
  if (!span.occupied) return result;
  bool has0 = span.lo <= 7;
  bool has1 = span.hi >= 8;
  if (has0) {
    result.strength0_hi = static_cast<StrengthLevel>(7 - span.lo);
    result.strength0_lo = static_cast<StrengthLevel>(7 - std::min(span.hi, 7));
  }
  if (has1) {
    result.strength1_lo = static_cast<StrengthLevel>(std::max(span.lo, 8) - 8);
    result.strength1_hi = static_cast<StrengthLevel>(span.hi - 8);
  }
  if (has0 && has1) {
    result.value = Val4::kX;
  } else if (has0) {
    result.value = Val4::kV0;
  } else {
    result.value = Val4::kV1;
  }
  return result;
}

// §28.12.4: the net types triand, wand, trior and wor "shall resolve conflicts
// when multiple drivers have the same strength", by "treating signals as inputs
// of logic functions". The result has "the same value as the result produced by
// an and gate" or "an or gate" with the two values as inputs, and "the strength
// of the result is the same as the strength of the combined signals".
//
// Two cells of unequal strength are not a conflict, and Figure 28-25's charts
// resolve such a pair to the stronger cell under both kinds of logic. The gate
// decides a pair of equal strength alone, and each cell carries the value of
// the side it stands on, so the gate is only ever handed a 0 and a 1.
inline int WiredPairPosition(int a, int b, ModelWiredLogicKind logic) {
  int stronger_a = a <= 7 ? 7 - a : a - 8;
  int stronger_b = b <= 7 ? 7 - b : b - 8;
  if (stronger_a > stronger_b) return a;
  if (stronger_b > stronger_a) return b;
  if (a == b) return a;
  // Equal strength and opposite values. `and` gives the 0 cell and `or` the 1
  // cell, the 0 cells being the positions at or below 7.
  bool want_zero = logic == ModelWiredLogicKind::kAnd;
  return want_zero ? std::min(a, b) : std::max(a, b);
}

// §28.12.4: "When ambiguous strength signals combine in wired logic, it is
// necessary to consider the results of all combinations of each of the strength
// levels in the first signal with each of the strength levels in the second
// signal, as shown in Figure 28-25." Every cell of one signal is resolved
// against every cell of the other, and the results are taken together as one
// range.
//
// Figure 28-25 is what fixes both halves. Its signal 1 occupies St0 and Pu0 and
// its signal 2 occupies Pu1. Under and logic the chart gives (5,0) and (6,0)
// and draws a result running from St0 to Pu0; under or logic it gives (5,1) and
// (6,0) and draws one running from St0 across to Pu1. The second is a range
// crossing both sides, which is why the result of a wired net can be ambiguous
// where neither of its two drivers was.
inline StrengthSignal CombineWithWiredLogic(StrengthSignal a, StrengthSignal b,
                                            ModelWiredLogicKind logic) {
  ScaleSpan span_a = SpanOf(a);
  ScaleSpan span_b = SpanOf(b);
  if (!span_a.occupied) return b;
  if (!span_b.occupied) return a;

  ScaleSpan result;
  for (int pa = span_a.lo; pa <= span_a.hi; ++pa) {
    for (int pb = span_b.lo; pb <= span_b.hi; ++pb) {
      ExtendSpan(result, WiredPairPosition(pa, pb, logic));
    }
  }
  return SignalOfSpan(result);
}

// §28.12.2: "The combination of two signals of ambiguous strength shall result
// in a signal of ambiguous strength. The resulting signal shall have a range of
// strength levels that includes the strength levels in its component signals",
// which Figure 28-9 and Figure 28-10 draw as "a range that includes the
// extremes of the signals and all the strengths between them".
//
// The extremes are taken over Figure 28-2's scale rather than per side, so a
// range whose two components sit on opposite sides crosses high impedance and
// covers it, and one whose components sit on one side keeps the lower bound
// they leave. Reading _hi alone gave every result a lower bound of high
// impedance, which is issue #3423.
inline StrengthSignal CombineAmbiguous(StrengthSignal a, StrengthSignal b) {
  ScaleSpan span_a = SpanOf(a);
  ScaleSpan span_b = SpanOf(b);
  if (!span_a.occupied) return b;
  if (!span_b.occupied) return a;
  ScaleSpan result = span_a;
  ExtendSpan(result, span_b.lo);
  ExtendSpan(result, span_b.hi);
  return SignalOfSpan(result);
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
