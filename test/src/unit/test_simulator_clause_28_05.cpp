// §28.5: buf and not gates

#include <cstdint>
#include <gtest/gtest.h>

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

Val4 EvalNInputGate(GateKind kind, Val4 a, Val4 b) {
  // Normalize z to x for input evaluation.
  Val4 na = (a == Val4::kZ) ? Val4::kX : a;
  Val4 nb = (b == Val4::kZ) ? Val4::kX : b;

  Val4 result = Val4::kX;
  switch (kind) {
  case GateKind::kAnd:
    if (na == Val4::kV0 || nb == Val4::kV0)
      result = Val4::kV0;
    else if (na == Val4::kV1 && nb == Val4::kV1)
      result = Val4::kV1;
    else
      result = Val4::kX;
    break;
  case GateKind::kOr:
    if (na == Val4::kV1 || nb == Val4::kV1)
      result = Val4::kV1;
    else if (na == Val4::kV0 && nb == Val4::kV0)
      result = Val4::kV0;
    else
      result = Val4::kX;
    break;
  case GateKind::kXor:
    if (na == Val4::kX || nb == Val4::kX)
      result = Val4::kX;
    else
      result = (na == nb) ? Val4::kV0 : Val4::kV1;
    break;
  case GateKind::kNand:
    result = InvertVal4(EvalNInputGate(GateKind::kAnd, a, b));
    break;
  case GateKind::kNor:
    result = InvertVal4(EvalNInputGate(GateKind::kOr, a, b));
    break;
  case GateKind::kXnor:
    result = InvertVal4(EvalNInputGate(GateKind::kXor, a, b));
    break;
  default:
    result = Val4::kX;
    break;
  }
  return result;
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
  if (d_rise == 0 && d_fall == 0)
    return 0;
  if (from == to)
    return 0;
  if (to == Val4::kV1)
    return d_rise;
  if (to == Val4::kV0)
    return d_fall;
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

} // namespace
