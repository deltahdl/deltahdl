// §28.5: buf and not gates

#include <gtest/gtest.h>

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

Val4 EvalNInputGate(GateKind kind, Val4 a, Val4 b);

Val4 EvalNOutputGate(GateKind kind, Val4 input);

uint64_t ComputeGateDelay(uint64_t d_rise, uint64_t d_fall, Val4 from, Val4 to);

// --- Implementations ---
static Val4 InvertVal4(Val4 v) {
  switch (v) {
    case Val4::kV0:
      return Val4::kV1;
    case Val4::kV1:
      return Val4::kV0;
    default:
      return Val4::kX;
  }
}

static Val4 NormalizeInput(Val4 v) {
  return (v == Val4::kZ) ? Val4::kX : v;
}

static Val4 EvalAnd(Val4 a, Val4 b) {
  if (a == Val4::kV0 || b == Val4::kV0) return Val4::kV0;
  if (a == Val4::kV1 && b == Val4::kV1) return Val4::kV1;
  return Val4::kX;
}

static Val4 EvalOr(Val4 a, Val4 b) {
  if (a == Val4::kV1 || b == Val4::kV1) return Val4::kV1;
  if (a == Val4::kV0 && b == Val4::kV0) return Val4::kV0;
  return Val4::kX;
}

static Val4 EvalXor(Val4 a, Val4 b) {
  if (a == Val4::kX || b == Val4::kX) return Val4::kX;
  return (a == b) ? Val4::kV0 : Val4::kV1;
}

Val4 EvalNInputGate(GateKind kind, Val4 a, Val4 b) {
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

Val4 EvalNOutputGate(GateKind kind, Val4 input) {
  // z is treated as x for buf/not gates.
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

uint64_t ComputeGateDelay(uint64_t d_rise, uint64_t d_fall, Val4 from,
                          Val4 to) {
  if (d_rise == 0 && d_fall == 0) return 0;
  if (from == to) return 0;
  if (to == Val4::kV1) return d_rise;
  if (to == Val4::kV0) return d_fall;
  // Transition to x or z: use the smaller of rise and fall.
  return (d_rise < d_fall) ? d_rise : d_fall;
}

namespace {

// =============================================================
// §28.5: buf and not gates
// =============================================================
// §28.5: Truth tables (Table 28-4)
TEST(LogicGates, BufGateTruthTable) {
  EXPECT_EQ(EvalNOutputGate(GateKind::kBuf, Val4::kV0), Val4::kV0);
  EXPECT_EQ(EvalNOutputGate(GateKind::kBuf, Val4::kV1), Val4::kV1);
  EXPECT_EQ(EvalNOutputGate(GateKind::kBuf, Val4::kX), Val4::kX);
  EXPECT_EQ(EvalNOutputGate(GateKind::kBuf, Val4::kZ), Val4::kX);
}

TEST(LogicGates, NotGateTruthTable) {
  EXPECT_EQ(EvalNOutputGate(GateKind::kNot, Val4::kV0), Val4::kV1);
  EXPECT_EQ(EvalNOutputGate(GateKind::kNot, Val4::kV1), Val4::kV0);
  EXPECT_EQ(EvalNOutputGate(GateKind::kNot, Val4::kX), Val4::kX);
  EXPECT_EQ(EvalNOutputGate(GateKind::kNot, Val4::kZ), Val4::kX);
}

}  // namespace
