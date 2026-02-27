// §28.3.2: The drive strength specification

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

// §28.3.2: "The strength specifications (highz0, highz1) and
//  (highz1, highz0) shall be considered invalid."
TEST(GateDecl, BothHighzStrengthsInvalid) {
  EXPECT_FALSE(ValidateStrengthSpec(StrengthLvl::kHighz, StrengthLvl::kHighz,
                                    GateType::kAnd));
}

// §28.3.2: "In the absence of a strength specification, the instances
//  shall have the default strengths strong1 and strong0."
TEST(GateDecl, DefaultStrengthIsStrong) {
  GateDeclInfo info;
  info.has_strength = false;
  EXPECT_TRUE(ValidateGateDecl(info));
}

}  // namespace
