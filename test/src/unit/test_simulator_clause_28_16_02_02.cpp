#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <initializer_list>

#include "helpers_mintymax.h"

struct DelaySpec {
  uint64_t d1 = 0;
  uint64_t d2 = 0;
  uint64_t d3 = 0;
  uint8_t count = 0;
};
bool ValidateTriregChargeDecaySpec(const DelaySpec& spec) {
  return spec.count == 3;
}

namespace {

TEST(TriregChargeDecay, ThreeDelaySpecValid) {
  DelaySpec spec{0, 0, 50, 3};
  EXPECT_TRUE(ValidateTriregChargeDecaySpec(spec));
}

TEST(TriregChargeDecay, OneDelayHasNoChargeDecay) {
  DelaySpec spec{10, 0, 0, 1};
  EXPECT_FALSE(ValidateTriregChargeDecaySpec(spec));
}

TEST(TriregChargeDecay, TwoDelaysHasNoChargeDecay) {
  DelaySpec spec{10, 20, 0, 2};
  EXPECT_FALSE(ValidateTriregChargeDecaySpec(spec));
}

}  // namespace
