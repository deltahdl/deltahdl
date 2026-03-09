#include <gtest/gtest.h>

#include "model_gate_declaration.h"

namespace {

TEST(GateDecl, StrengthSpecValidForPullGates) {
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kPullup));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kPulldown));
}

TEST(GateDecl, StrengthSpecInvalidForSwitches) {
  EXPECT_FALSE(CanHaveStrengthSpec(GateType::kNmos));
  EXPECT_FALSE(CanHaveStrengthSpec(GateType::kPmos));
  EXPECT_FALSE(CanHaveStrengthSpec(GateType::kTran));
  EXPECT_FALSE(CanHaveStrengthSpec(GateType::kCmos));
}

TEST(GateDecl, BothHighzStrengthsInvalid) {
  EXPECT_FALSE(ValidateStrengthSpec(StrengthLvl::kHighz, StrengthLvl::kHighz,
                                    GateType::kAnd));
}

TEST(GateDecl, DefaultStrengthIsStrong) {
  GateDeclInfo info;
  info.has_strength = false;
  EXPECT_TRUE(ValidateGateDecl(info));
}

}  // namespace
