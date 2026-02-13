#include <gtest/gtest.h>

#include <cstdint>

// --- Local types for logic gate evaluation (§28.4, §28.5) ---

enum class Val4 : uint8_t { kV0 = 0, kV1 = 1, kX = 2, kZ = 3 };

enum class GateKind : uint8_t {
  kAnd, kNand, kOr, kNor, kXor, kXnor, kBuf, kNot
};

Val4 EvalNInputGate(GateKind kind, Val4 a, Val4 b);
Val4 EvalNOutputGate(GateKind kind, Val4 input);
uint64_t ComputeGateDelay(uint64_t d_rise, uint64_t d_fall,
                          Val4 from, Val4 to);

// =============================================================
// §28.4: and, nand, nor, or, xor, and xnor gates
// =============================================================

// §28.4: Truth tables (Table 28-3)
TEST(LogicGates, AndGateTruthTable) {
  // Row 0
  EXPECT_EQ(EvalNInputGate(GateKind::kAnd, Val4::kV0, Val4::kV0), Val4::kV0);
  EXPECT_EQ(EvalNInputGate(GateKind::kAnd, Val4::kV0, Val4::kV1), Val4::kV0);
  EXPECT_EQ(EvalNInputGate(GateKind::kAnd, Val4::kV0, Val4::kX), Val4::kV0);
  EXPECT_EQ(EvalNInputGate(GateKind::kAnd, Val4::kV0, Val4::kZ), Val4::kV0);
  // Row 1
  EXPECT_EQ(EvalNInputGate(GateKind::kAnd, Val4::kV1, Val4::kV0), Val4::kV0);
  EXPECT_EQ(EvalNInputGate(GateKind::kAnd, Val4::kV1, Val4::kV1), Val4::kV1);
  EXPECT_EQ(EvalNInputGate(GateKind::kAnd, Val4::kV1, Val4::kX), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kAnd, Val4::kV1, Val4::kZ), Val4::kX);
  // Row x
  EXPECT_EQ(EvalNInputGate(GateKind::kAnd, Val4::kX, Val4::kV0), Val4::kV0);
  EXPECT_EQ(EvalNInputGate(GateKind::kAnd, Val4::kX, Val4::kV1), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kAnd, Val4::kX, Val4::kX), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kAnd, Val4::kX, Val4::kZ), Val4::kX);
  // Row z
  EXPECT_EQ(EvalNInputGate(GateKind::kAnd, Val4::kZ, Val4::kV0), Val4::kV0);
  EXPECT_EQ(EvalNInputGate(GateKind::kAnd, Val4::kZ, Val4::kV1), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kAnd, Val4::kZ, Val4::kX), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kAnd, Val4::kZ, Val4::kZ), Val4::kX);
}

TEST(LogicGates, OrGateTruthTable) {
  EXPECT_EQ(EvalNInputGate(GateKind::kOr, Val4::kV0, Val4::kV0), Val4::kV0);
  EXPECT_EQ(EvalNInputGate(GateKind::kOr, Val4::kV0, Val4::kV1), Val4::kV1);
  EXPECT_EQ(EvalNInputGate(GateKind::kOr, Val4::kV0, Val4::kX), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kOr, Val4::kV0, Val4::kZ), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kOr, Val4::kV1, Val4::kV0), Val4::kV1);
  EXPECT_EQ(EvalNInputGate(GateKind::kOr, Val4::kV1, Val4::kV1), Val4::kV1);
  EXPECT_EQ(EvalNInputGate(GateKind::kOr, Val4::kV1, Val4::kX), Val4::kV1);
  EXPECT_EQ(EvalNInputGate(GateKind::kOr, Val4::kV1, Val4::kZ), Val4::kV1);
  EXPECT_EQ(EvalNInputGate(GateKind::kOr, Val4::kX, Val4::kV0), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kOr, Val4::kX, Val4::kV1), Val4::kV1);
  EXPECT_EQ(EvalNInputGate(GateKind::kOr, Val4::kX, Val4::kX), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kOr, Val4::kX, Val4::kZ), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kOr, Val4::kZ, Val4::kV0), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kOr, Val4::kZ, Val4::kV1), Val4::kV1);
  EXPECT_EQ(EvalNInputGate(GateKind::kOr, Val4::kZ, Val4::kX), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kOr, Val4::kZ, Val4::kZ), Val4::kX);
}

TEST(LogicGates, XorGateTruthTable) {
  EXPECT_EQ(EvalNInputGate(GateKind::kXor, Val4::kV0, Val4::kV0), Val4::kV0);
  EXPECT_EQ(EvalNInputGate(GateKind::kXor, Val4::kV0, Val4::kV1), Val4::kV1);
  EXPECT_EQ(EvalNInputGate(GateKind::kXor, Val4::kV0, Val4::kX), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kXor, Val4::kV0, Val4::kZ), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kXor, Val4::kV1, Val4::kV0), Val4::kV1);
  EXPECT_EQ(EvalNInputGate(GateKind::kXor, Val4::kV1, Val4::kV1), Val4::kV0);
  EXPECT_EQ(EvalNInputGate(GateKind::kXor, Val4::kV1, Val4::kX), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kXor, Val4::kV1, Val4::kZ), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kXor, Val4::kX, Val4::kV0), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kXor, Val4::kX, Val4::kV1), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kXor, Val4::kX, Val4::kX), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kXor, Val4::kX, Val4::kZ), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kXor, Val4::kZ, Val4::kV0), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kXor, Val4::kZ, Val4::kV1), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kXor, Val4::kZ, Val4::kX), Val4::kX);
  EXPECT_EQ(EvalNInputGate(GateKind::kXor, Val4::kZ, Val4::kZ), Val4::kX);
}

// §28.4: nand = NOT(and), nor = NOT(or), xnor = NOT(xor)
TEST(LogicGates, NandIsInvertedAnd) {
  Val4 vals[] = {Val4::kV0, Val4::kV1, Val4::kX, Val4::kZ};
  for (Val4 a : vals) {
    for (Val4 b : vals) {
      Val4 and_result = EvalNInputGate(GateKind::kAnd, a, b);
      Val4 nand_result = EvalNInputGate(GateKind::kNand, a, b);
      if (and_result == Val4::kV0) EXPECT_EQ(nand_result, Val4::kV1);
      if (and_result == Val4::kV1) EXPECT_EQ(nand_result, Val4::kV0);
      if (and_result == Val4::kX) EXPECT_EQ(nand_result, Val4::kX);
    }
  }
}

TEST(LogicGates, NorIsInvertedOr) {
  Val4 vals[] = {Val4::kV0, Val4::kV1, Val4::kX, Val4::kZ};
  for (Val4 a : vals) {
    for (Val4 b : vals) {
      Val4 or_result = EvalNInputGate(GateKind::kOr, a, b);
      Val4 nor_result = EvalNInputGate(GateKind::kNor, a, b);
      if (or_result == Val4::kV0) EXPECT_EQ(nor_result, Val4::kV1);
      if (or_result == Val4::kV1) EXPECT_EQ(nor_result, Val4::kV0);
      if (or_result == Val4::kX) EXPECT_EQ(nor_result, Val4::kX);
    }
  }
}

TEST(LogicGates, XnorIsInvertedXor) {
  Val4 vals[] = {Val4::kV0, Val4::kV1, Val4::kX, Val4::kZ};
  for (Val4 a : vals) {
    for (Val4 b : vals) {
      Val4 xor_result = EvalNInputGate(GateKind::kXor, a, b);
      Val4 xnor_result = EvalNInputGate(GateKind::kXnor, a, b);
      if (xor_result == Val4::kV0) EXPECT_EQ(xnor_result, Val4::kV1);
      if (xor_result == Val4::kV1) EXPECT_EQ(xnor_result, Val4::kV0);
      if (xor_result == Val4::kX) EXPECT_EQ(xnor_result, Val4::kX);
    }
  }
}

// §28.4: Two delays — "the first delay shall determine the output rise
//  delay, the second delay shall determine the output fall delay, and
//  the smaller of the two delays shall apply to output transitions to x."
TEST(LogicGates, TwoDelayRiseFallAndX) {
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV0, Val4::kV1), 10u);  // rise
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV1, Val4::kV0), 12u);  // fall
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV0, Val4::kX), 10u);   // min
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV1, Val4::kX), 10u);   // min
}

// §28.4: "If only one delay is specified, it shall specify both the
//  rise delay and the fall delay."
TEST(LogicGates, SingleDelayUsedForAll) {
  EXPECT_EQ(ComputeGateDelay(10, 10, Val4::kV0, Val4::kV1), 10u);
  EXPECT_EQ(ComputeGateDelay(10, 10, Val4::kV1, Val4::kV0), 10u);
}

// §28.4: "If there is no delay specification, there shall be no
//  propagation delay through the gate."
TEST(LogicGates, NoDelayZeroPropagation) {
  EXPECT_EQ(ComputeGateDelay(0, 0, Val4::kV0, Val4::kV1), 0u);
}

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

// §28.5: "These two logic gates shall have one input and one or more
//  outputs. The last terminal in the terminal list shall connect to the
//  input of the logic gate."
