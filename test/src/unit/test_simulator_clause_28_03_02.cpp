#include <gtest/gtest.h>

#include "model_gate_declaration.h"

namespace {

TEST(HighzStrengthOutput, Highz1ProducesZ) {
  EXPECT_TRUE(ValidateStrengthSpec(StrengthLvl::kStrong, StrengthLvl::kHighz,
                                   GateType::kNor));
}

TEST(HighzStrengthOutput, Highz0ProducesZ) {
  EXPECT_TRUE(ValidateStrengthSpec(StrengthLvl::kHighz, StrengthLvl::kStrong,
                                   GateType::kAnd));
}

}
