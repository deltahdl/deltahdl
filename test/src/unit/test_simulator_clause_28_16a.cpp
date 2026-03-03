// Non-LRM tests

#include <gtest/gtest.h>
#include <algorithm>
#include <cstdint>
#include <initializer_list>

// --- Local types for gate/net delays (§28.16) ---
enum class Val4 : uint8_t { kV0 = 0, kV1 = 1, kX = 2, kZ = 3 };

struct DelaySpec {
  uint64_t d1 = 0;    // rise
  uint64_t d2 = 0;    // fall
  uint64_t d3 = 0;    // turn-off (z) or charge decay for trireg
  uint8_t count = 0;  // 0, 1, 2, or 3
};

enum class ChargeDecayState : uint8_t { kIdle, kDecaying, kDone };

bool ValidateTriregChargeDecaySpec(const DelaySpec& spec) {
  return spec.count == 3;
}

namespace {

// §28.16.2.2: One or two delays → no charge decay.
TEST(TriregChargeDecay, OneDelayHasNoChargeDecay) {
  DelaySpec spec{10, 0, 0, 1};
  EXPECT_FALSE(ValidateTriregChargeDecaySpec(spec));
}

TEST(TriregChargeDecay, TwoDelaysHasNoChargeDecay) {
  DelaySpec spec{10, 20, 0, 2};
  EXPECT_FALSE(ValidateTriregChargeDecaySpec(spec));
}

}  // namespace
