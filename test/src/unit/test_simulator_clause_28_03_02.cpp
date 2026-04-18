#include <gtest/gtest.h>

#include "model_gate_declaration.h"

namespace {

TEST(HighzStrengthOutput, Highz1ProducesZ) {
  EXPECT_TRUE(ValidateStrengthSpec(StrengthLvl::kStrong, StrengthLvl::kHighz,
                                   GateType::kNor));
}

// highz0 paired with a non-highz strength1 is a valid spec; the output-z
// behaviour for a logic-0 value is the simulator's responsibility, not a
// validation failure.
TEST(HighzStrengthOutput, Highz0ProducesZ) {
  EXPECT_TRUE(ValidateStrengthSpec(StrengthLvl::kHighz, StrengthLvl::kStrong,
                                   GateType::kAnd));
}

}  // namespace
