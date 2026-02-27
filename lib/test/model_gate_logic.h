#pragma once

#include <cstdint>

// --- Local types for logic gate evaluation (§28.4, §28.5) ---
enum class Val4 : uint8_t { kV0 = 0, kV1 = 1, kX = 2, kZ = 3 };

enum class GateKind : uint8_t {
  kAnd,
  kNand,
  kOr,
  kNor,
  kXor,
  kXnor,
  kBuf,
  kNot
};

inline Val4 InvertVal4(Val4 v);
inline Val4 NormalizeInput(Val4 v);
inline Val4 EvalAnd(Val4 a, Val4 b);
inline Val4 EvalOr(Val4 a, Val4 b);
inline Val4 EvalXor(Val4 a, Val4 b);
inline Val4 EvalNInputGate(GateKind kind, Val4 a, Val4 b);
inline Val4 EvalNOutputGate(GateKind kind, Val4 input);
inline uint64_t ComputeGateDelay(uint64_t d_rise, uint64_t d_fall, Val4 from,
                                 Val4 to);

// --- Implementations ---
inline Val4 InvertVal4(Val4 v) {
  switch (v) {
    case Val4::kV0:
      return Val4::kV1;
    case Val4::kV1:
      return Val4::kV0;
    default:
      return Val4::kX;
  }
}

inline Val4 NormalizeInput(Val4 v) {
  return (v == Val4::kZ) ? Val4::kX : v;
}

inline Val4 EvalAnd(Val4 a, Val4 b) {
  if (a == Val4::kV0 || b == Val4::kV0) return Val4::kV0;
  if (a == Val4::kV1 && b == Val4::kV1) return Val4::kV1;
  return Val4::kX;
}

inline Val4 EvalOr(Val4 a, Val4 b) {
  if (a == Val4::kV1 || b == Val4::kV1) return Val4::kV1;
  if (a == Val4::kV0 && b == Val4::kV0) return Val4::kV0;
  return Val4::kX;
}

inline Val4 EvalXor(Val4 a, Val4 b) {
  if (a == Val4::kX || b == Val4::kX) return Val4::kX;
  return (a == b) ? Val4::kV0 : Val4::kV1;
}

inline Val4 EvalNInputGate(GateKind kind, Val4 a, Val4 b) {
  Val4 na = NormalizeInput(a);
  Val4 nb = NormalizeInput(b);
  switch (kind) {
    case GateKind::kAnd:
      return EvalAnd(na, nb);
    case GateKind::kOr:
      return EvalOr(na, nb);
    case GateKind::kXor:
      return EvalXor(na, nb);
    case GateKind::kNand:
      return InvertVal4(EvalAnd(na, nb));
    case GateKind::kNor:
      return InvertVal4(EvalOr(na, nb));
    case GateKind::kXnor:
      return InvertVal4(EvalXor(na, nb));
    default:
      return Val4::kX;
  }
}

inline Val4 EvalNOutputGate(GateKind kind, Val4 input) {
  Val4 ni = (input == Val4::kZ) ? Val4::kX : input;
  switch (kind) {
    case GateKind::kBuf:
      return ni;
    case GateKind::kNot:
      return InvertVal4(ni);
    default:
      return Val4::kX;
  }
}

inline uint64_t ComputeGateDelay(uint64_t d_rise, uint64_t d_fall, Val4 from,
                                 Val4 to) {
  if (d_rise == 0 && d_fall == 0) return 0;
  if (from == to) return 0;
  if (to == Val4::kV1) return d_rise;
  if (to == Val4::kV0) return d_fall;
  return (d_rise < d_fall) ? d_rise : d_fall;
}
