// §28.5: buf and not gates

#include <gtest/gtest.h>

#include "model_gate_logic.h"

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
