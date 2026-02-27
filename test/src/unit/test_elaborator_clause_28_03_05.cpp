// §28.3.5: The range specification

#include <gtest/gtest.h>

#include "model_gate_declaration.h"

namespace {

// --- §28.3.5: Range specification ---
// §28.3.5: "abs(lhi-rhi)+1 instances"
TEST(GateDecl, ArraySizeComputation) {
  EXPECT_EQ(ComputeArraySize(0, 3), 4u);
  EXPECT_EQ(ComputeArraySize(3, 0), 4u);
  EXPECT_EQ(ComputeArraySize(1, 4), 4u);
}

// §28.3.5: "lhi is not required to be larger than rhi."
TEST(GateDecl, LhiNotRequiredLargerThanRhi) {
  EXPECT_EQ(ComputeArraySize(7, 0), 8u);
  EXPECT_EQ(ComputeArraySize(0, 7), 8u);
}

// §28.3.5: "If both constant expressions are equal, only one instance
//  shall be generated."
TEST(GateDecl, EqualRangeBoundsOneInstance) {
  EXPECT_EQ(ComputeArraySize(5, 5), 1u);
}

// §28.3.5: "If no range specification is given, a single instance
//  shall be created."
TEST(GateDecl, NoRangeSingleInstance) {
  GateDeclInfo info;
  info.has_range = false;
  info.has_name = true;
  info.terminal_count = 3;
  EXPECT_TRUE(ValidateGateDecl(info));
}

}  // namespace
