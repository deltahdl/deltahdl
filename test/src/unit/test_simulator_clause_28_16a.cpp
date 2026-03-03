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

struct MinTypMax {
  uint64_t min_val = 0;
  uint64_t typ_val = 0;
  uint64_t max_val = 0;
};

enum class ChargeDecayState : uint8_t { kIdle, kDecaying, kDone };

uint64_t SelectMinTypMax(const MinTypMax& mtm, uint8_t selector) {
  switch (selector) {
    case 0:
      return mtm.min_val;
    case 1:
      return mtm.typ_val;
    case 2:
      return mtm.max_val;
    default:
      return mtm.typ_val;
  }
}

bool ValidateTriregChargeDecaySpec(const DelaySpec& spec) {
  return spec.count == 3;
}

namespace {

TEST(MinTypMaxDelays, SelectMax) {
  MinTypMax mtm{5, 10, 15};
  EXPECT_EQ(SelectMinTypMax(mtm, 2), 15u);
}

// §28.16.1: No required relation — max can be less than min.
TEST(MinTypMaxDelays, NoRequiredOrdering) {
  MinTypMax mtm{20, 5, 10};
  EXPECT_EQ(SelectMinTypMax(mtm, 0), 20u);
  EXPECT_EQ(SelectMinTypMax(mtm, 1), 5u);
  EXPECT_EQ(SelectMinTypMax(mtm, 2), 10u);
}

// =============================================================
// §28.16.2: trireg net charge decay
// =============================================================
// §28.16.2: "The first two delays shall specify the delay for
//  transition to the 1 and 0 logic states when the trireg net is
//  driven to these states by a driver."
// §28.16.2: "The third delay shall specify the charge decay time
//  instead of the delay in a transition to the z logic state."
// §28.16.2.2: "The charge decay time specification in a trireg net
//  declaration shall be preceded by a rise and a fall delay
//  specification."
TEST(TriregChargeDecay, ThreeDelaySpecValid) {
  DelaySpec spec{0, 0, 50, 3};
  EXPECT_TRUE(ValidateTriregChargeDecaySpec(spec));
}

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
