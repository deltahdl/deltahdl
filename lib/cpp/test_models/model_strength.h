#pragma once

#include <algorithm>
#include <cstdint>

#include "model_val4.h"

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

struct StrengthSignal {
  Val4 value = Val4::kZ;
  StrengthLevel strength0_hi = StrengthLevel::kHighz;
  StrengthLevel strength1_hi = StrengthLevel::kHighz;
  StrengthLevel strength0_lo = StrengthLevel::kHighz;
  StrengthLevel strength1_lo = StrengthLevel::kHighz;
};

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

inline bool ValidateStrengthPair(StrengthLevel s0, StrengthLevel s1) {
  return s0 != StrengthLevel::kHighz || s1 != StrengthLevel::kHighz;
}

inline StrengthSignal CombineUnambiguous(StrengthSignal a, StrengthSignal b) {
  auto effective = [](const StrengthSignal& s) -> StrengthLevel {
    return std::max(s.strength0_hi, s.strength1_hi);
  };

  StrengthLevel eff_a = effective(a);
  StrengthLevel eff_b = effective(b);

  if (a.value == b.value) {
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

  if (eff_a > eff_b) {
    return a;
  } else if (eff_b > eff_a) {
    return b;
  }

  StrengthSignal result;
  result.value = Val4::kX;
  result.strength0_hi = eff_a;
  result.strength0_lo = eff_a;
  result.strength1_hi = eff_a;
  result.strength1_lo = eff_a;
  return result;
}

inline int ScalePositionOf(StrengthLevel level, bool side_is_1) {
  int index = static_cast<int>(level);
  return side_is_1 ? 8 + index : 7 - index;
}

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

inline int WiredPairPosition(int a, int b, ModelWiredLogicKind logic) {
  int stronger_a = a <= 7 ? 7 - a : a - 8;
  int stronger_b = b <= 7 ? 7 - b : b - 8;
  if (stronger_a > stronger_b) return a;
  if (stronger_b > stronger_a) return b;
  if (a == b) return a;
  bool want_zero = logic == ModelWiredLogicKind::kAnd;
  return want_zero ? std::min(a, b) : std::max(a, b);
}

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

inline StrengthSignal CombineAmbiguousWithUnambiguous(StrengthSignal unambig,
                                                      StrengthSignal ambig) {
  bool vu_is_0 = unambig.value == Val4::kV0;
  StrengthLevel s_u = vu_is_0 ? unambig.strength0_hi : unambig.strength1_hi;
  auto s_u_idx = static_cast<uint8_t>(s_u);

  StrengthLevel amb_vu_lo = vu_is_0 ? ambig.strength0_lo : ambig.strength1_lo;
  StrengthLevel amb_vu_hi = vu_is_0 ? ambig.strength0_hi : ambig.strength1_hi;
  StrengthLevel amb_op_hi = vu_is_0 ? ambig.strength1_hi : ambig.strength0_hi;

  bool opposite_survives = static_cast<uint8_t>(amb_op_hi) > s_u_idx;

  StrengthLevel vu_hi = static_cast<StrengthLevel>(
      std::max<uint8_t>(s_u_idx, static_cast<uint8_t>(amb_vu_hi)));
  StrengthLevel vu_lo = opposite_survives
                            ? StrengthLevel::kHighz
                            : static_cast<StrengthLevel>(std::max<uint8_t>(
                                  s_u_idx, static_cast<uint8_t>(amb_vu_lo)));
  StrengthLevel op_hi = opposite_survives ? amb_op_hi : StrengthLevel::kHighz;
  StrengthLevel op_lo = StrengthLevel::kHighz;

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

  result.value = opposite_survives ? Val4::kX : unambig.value;
  return result;
}

inline StrengthLevel ModelReduceNonresistive(StrengthLevel input) {
  if (input == StrengthLevel::kSupply) {
    return StrengthLevel::kStrong;
  }
  return input;
}

inline StrengthLevel ModelReduceResistive(StrengthLevel input) {
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
