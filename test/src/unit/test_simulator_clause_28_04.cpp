// §28.4: and, nand, nor, or, xor, and xnor gates

#include <gtest/gtest.h>

#include <initializer_list>
#include <tuple>

#include "model_gate_logic.h"

using GateTruthEntry = std::tuple<Val4, Val4, Val4>;

static void RunGateTruthTable(GateKind kind,
                              std::initializer_list<GateTruthEntry> cases,
                              const char* label) {
  for (auto& [a, b, expected] : cases) {
    EXPECT_EQ(EvalNInputGate(kind, a, b), expected)
        << label << " a=" << static_cast<int>(a)
        << " b=" << static_cast<int>(b);
  }
}

namespace {

// =============================================================
// §28.4: and, nand, nor, or, xor, and xnor gates
// =============================================================
// §28.4: Truth tables (Table 28-3)
TEST(LogicGates, AndGateTruthTable) {
  RunGateTruthTable(GateKind::kAnd,
                    {
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
                    },
                    "And");
}

TEST(LogicGates, OrGateTruthTable) {
  RunGateTruthTable(GateKind::kOr,
                    {
                        {Val4::kV0, Val4::kV0, Val4::kV0},
                        {Val4::kV0, Val4::kV1, Val4::kV1},
                        {Val4::kV0, Val4::kX, Val4::kX},
                        {Val4::kV0, Val4::kZ, Val4::kX},
                        {Val4::kV1, Val4::kV0, Val4::kV1},
                        {Val4::kV1, Val4::kV1, Val4::kV1},
                        {Val4::kV1, Val4::kX, Val4::kV1},
                        {Val4::kV1, Val4::kZ, Val4::kV1},
                        {Val4::kX, Val4::kV0, Val4::kX},
                        {Val4::kX, Val4::kV1, Val4::kV1},
                        {Val4::kX, Val4::kX, Val4::kX},
                        {Val4::kX, Val4::kZ, Val4::kX},
                        {Val4::kZ, Val4::kV0, Val4::kX},
                        {Val4::kZ, Val4::kV1, Val4::kV1},
                        {Val4::kZ, Val4::kX, Val4::kX},
                        {Val4::kZ, Val4::kZ, Val4::kX},
                    },
                    "Or");
}

TEST(LogicGates, XorGateTruthTable) {
  RunGateTruthTable(GateKind::kXor,
                    {
                        {Val4::kV0, Val4::kV0, Val4::kV0},
                        {Val4::kV0, Val4::kV1, Val4::kV1},
                        {Val4::kV0, Val4::kX, Val4::kX},
                        {Val4::kV0, Val4::kZ, Val4::kX},
                        {Val4::kV1, Val4::kV0, Val4::kV1},
                        {Val4::kV1, Val4::kV1, Val4::kV0},
                        {Val4::kV1, Val4::kX, Val4::kX},
                        {Val4::kV1, Val4::kZ, Val4::kX},
                        {Val4::kX, Val4::kV0, Val4::kX},
                        {Val4::kX, Val4::kV1, Val4::kX},
                        {Val4::kX, Val4::kX, Val4::kX},
                        {Val4::kX, Val4::kZ, Val4::kX},
                        {Val4::kZ, Val4::kV0, Val4::kX},
                        {Val4::kZ, Val4::kV1, Val4::kX},
                        {Val4::kZ, Val4::kX, Val4::kX},
                        {Val4::kZ, Val4::kZ, Val4::kX},
                    },
                    "Xor");
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
