// §28.16: Gate and net delays

#include <gtest/gtest.h>

#include "model_gate_logic.h"

namespace {

// §28.4: Two delays — "the first delay shall determine the output rise
//  delay, the second delay shall determine the output fall delay, and
//  the smaller of the two delays shall apply to output transitions to x."
TEST(LogicGates, TwoDelayRiseFallAndX) {
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV0, Val4::kV1), 10u);  // rise
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV1, Val4::kV0), 12u);  // fall
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV0, Val4::kX), 10u);   // min
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV1, Val4::kX), 10u);   // min
}

// §28.4: "If there is no delay specification, there shall be no
//  propagation delay through the gate."
TEST(LogicGates, NoDelayZeroPropagation) {
  EXPECT_EQ(ComputeGateDelay(0, 0, Val4::kV0, Val4::kV1), 0u);
}

}  // namespace
