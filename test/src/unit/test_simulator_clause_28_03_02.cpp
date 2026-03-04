#include <gtest/gtest.h>

#include "model_gate_declaration.h"

namespace {

TEST(GateDecl, Highz1OutputsZInsteadOf1) {
  EXPECT_TRUE(ValidateStrengthSpec(StrengthLvl::kStrong, StrengthLvl::kHighz,
                                   GateType::kNor));
}

}  // namespace
