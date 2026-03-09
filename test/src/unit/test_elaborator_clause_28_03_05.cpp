#include <gtest/gtest.h>

#include "model_gate_declaration.h"

namespace {

TEST(GateDecl, ArraySizeComputation) {
  EXPECT_EQ(ComputeArraySize(0, 3), 4u);
  EXPECT_EQ(ComputeArraySize(3, 0), 4u);
  EXPECT_EQ(ComputeArraySize(1, 4), 4u);
}

TEST(GateDecl, LhiNotRequiredLargerThanRhi) {
  EXPECT_EQ(ComputeArraySize(7, 0), 8u);
  EXPECT_EQ(ComputeArraySize(0, 7), 8u);
}

TEST(GateDecl, EqualRangeBoundsOneInstance) {
  EXPECT_EQ(ComputeArraySize(5, 5), 1u);
}

TEST(GateDecl, NoRangeSingleInstance) {
  GateDeclInfo info;
  info.has_range = false;
  info.has_name = true;
  info.terminal_count = 3;
  EXPECT_TRUE(ValidateGateDecl(info));
}

}  // namespace
