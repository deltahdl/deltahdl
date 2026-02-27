// §28.3.2: The drive strength specification

#include <gtest/gtest.h>

#include "model_gate_declaration.h"

namespace {

// §28.3.2: highz1 → output z instead of 1.
TEST(GateDecl, Highz1OutputsZInsteadOf1) {
  EXPECT_TRUE(ValidateStrengthSpec(StrengthLvl::kStrong, StrengthLvl::kHighz,
                                   GateType::kNor));
}

}  // namespace
