// Non-LRM tests

#include <gtest/gtest.h>
#include "model_gate_logic.h"

namespace {

// §28.4: "If there is no delay specification, there shall be no
//  propagation delay through the gate."
TEST(LogicGates, NoDelayZeroPropagation) {
  EXPECT_EQ(ComputeGateDelay(0, 0, Val4::kV0, Val4::kV1), 0u);
}

}  // namespace
