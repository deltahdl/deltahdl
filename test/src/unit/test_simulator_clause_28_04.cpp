// §28.4: and, nand, nor, or, xor, and xnor gates

#include <gtest/gtest.h>

#include "model_gate_logic.h"

namespace {

// =============================================================
// §28.4: and, nand, nor, or, xor, and xnor gates
// =============================================================
// §28.4: Truth tables (Table 28-3)
TEST(LogicGates, AndGateTruthTable) {
  struct Case {
    Val4 a;
    Val4 b;
    Val4 expected;
  };
  Case cases[] = {
      // Row 0
      {Val4::kV0, Val4::kV0, Val4::kV0},
      {Val4::kV0, Val4::kV1, Val4::kV0},
      {Val4::kV0, Val4::kX, Val4::kV0},
      {Val4::kV0, Val4::kZ, Val4::kV0},
      // Row 1
      {Val4::kV1, Val4::kV0, Val4::kV0},
      {Val4::kV1, Val4::kV1, Val4::kV1},
      {Val4::kV1, Val4::kX, Val4::kX},
      {Val4::kV1, Val4::kZ, Val4::kX},
      // Row x
      {Val4::kX, Val4::kV0, Val4::kV0},
      {Val4::kX, Val4::kV1, Val4::kX},
      {Val4::kX, Val4::kX, Val4::kX},
      {Val4::kX, Val4::kZ, Val4::kX},
      // Row z
      {Val4::kZ, Val4::kV0, Val4::kV0},
      {Val4::kZ, Val4::kV1, Val4::kX},
      {Val4::kZ, Val4::kX, Val4::kX},
      {Val4::kZ, Val4::kZ, Val4::kX},
  };
  for (const auto& c : cases) {
    EXPECT_EQ(EvalNInputGate(GateKind::kAnd, c.a, c.b), c.expected)
        << "And(" << static_cast<int>(c.a) << ", " << static_cast<int>(c.b)
        << ")";
  }
}

TEST(LogicGates, OrGateTruthTable) {
  struct Case {
    Val4 a;
    Val4 b;
    Val4 expected;
  };
  Case cases[] = {
      {Val4::kV0, Val4::kV0, Val4::kV0}, {Val4::kV0, Val4::kV1, Val4::kV1},
      {Val4::kV0, Val4::kX, Val4::kX},   {Val4::kV0, Val4::kZ, Val4::kX},
      {Val4::kV1, Val4::kV0, Val4::kV1}, {Val4::kV1, Val4::kV1, Val4::kV1},
      {Val4::kV1, Val4::kX, Val4::kV1},  {Val4::kV1, Val4::kZ, Val4::kV1},
      {Val4::kX, Val4::kV0, Val4::kX},   {Val4::kX, Val4::kV1, Val4::kV1},
      {Val4::kX, Val4::kX, Val4::kX},    {Val4::kX, Val4::kZ, Val4::kX},
      {Val4::kZ, Val4::kV0, Val4::kX},   {Val4::kZ, Val4::kV1, Val4::kV1},
      {Val4::kZ, Val4::kX, Val4::kX},    {Val4::kZ, Val4::kZ, Val4::kX},
  };
  for (const auto& c : cases) {
    EXPECT_EQ(EvalNInputGate(GateKind::kOr, c.a, c.b), c.expected)
        << "Or(" << static_cast<int>(c.a) << ", " << static_cast<int>(c.b)
        << ")";
  }
}

TEST(LogicGates, XorGateTruthTable) {
  struct Case {
    Val4 a;
    Val4 b;
    Val4 expected;
  };
  Case cases[] = {
      {Val4::kV0, Val4::kV0, Val4::kV0}, {Val4::kV0, Val4::kV1, Val4::kV1},
      {Val4::kV0, Val4::kX, Val4::kX},   {Val4::kV0, Val4::kZ, Val4::kX},
      {Val4::kV1, Val4::kV0, Val4::kV1}, {Val4::kV1, Val4::kV1, Val4::kV0},
      {Val4::kV1, Val4::kX, Val4::kX},   {Val4::kV1, Val4::kZ, Val4::kX},
      {Val4::kX, Val4::kV0, Val4::kX},   {Val4::kX, Val4::kV1, Val4::kX},
      {Val4::kX, Val4::kX, Val4::kX},    {Val4::kX, Val4::kZ, Val4::kX},
      {Val4::kZ, Val4::kV0, Val4::kX},   {Val4::kZ, Val4::kV1, Val4::kX},
      {Val4::kZ, Val4::kX, Val4::kX},    {Val4::kZ, Val4::kZ, Val4::kX},
  };
  for (const auto& c : cases) {
    EXPECT_EQ(EvalNInputGate(GateKind::kXor, c.a, c.b), c.expected)
        << "Xor(" << static_cast<int>(c.a) << ", " << static_cast<int>(c.b)
        << ")";
  }
}

// §28.4: nand = NOT(and), nor = NOT(or), xnor = NOT(xor)
TEST(LogicGates, NandIsInvertedAnd) {
  CheckInversion(GateKind::kAnd, GateKind::kNand);
}

TEST(LogicGates, NorIsInvertedOr) {
  CheckInversion(GateKind::kOr, GateKind::kNor);
}

TEST(LogicGates, XnorIsInvertedXor) {
  CheckInversion(GateKind::kXor, GateKind::kXnor);
}

}  // namespace
