// §28.16: Gate and net delays

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

// §28.4: Two delays — "the first delay shall determine the output rise
//  delay, the second delay shall determine the output fall delay, and
//  the smaller of the two delays shall apply to output transitions to x."
TEST(LogicGates, TwoDelayRiseFallAndX) {
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV0, Val4::kV1), 10u); // rise
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV1, Val4::kV0), 12u); // fall
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV0, Val4::kX), 10u);  // min
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV1, Val4::kX), 10u);  // min
}

// §28.4: "If there is no delay specification, there shall be no
//  propagation delay through the gate."
TEST(LogicGates, NoDelayZeroPropagation) {
  EXPECT_EQ(ComputeGateDelay(0, 0, Val4::kV0, Val4::kV1), 0u);
}

} // namespace
