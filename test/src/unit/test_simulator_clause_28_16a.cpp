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

uint64_t ComputePropagationDelay(const DelaySpec& spec, Val4 from, Val4 to) {
  if (spec.count == 0) return 0;
  if (spec.count == 1) return spec.d1;
  if (from == to) return 0;
  if (spec.count == 2) {
    switch (to) {
      case Val4::kV1:
        return spec.d1;
      case Val4::kV0:
        return spec.d2;
      case Val4::kZ:
      case Val4::kX:
        return std::min(spec.d1, spec.d2);
    }
  }
  // count == 3
  switch (to) {
    case Val4::kV1:
      return spec.d1;
    case Val4::kV0:
      return spec.d2;
    case Val4::kZ:
      return spec.d3;
    case Val4::kX:
      return std::min({spec.d1, spec.d2, spec.d3});
  }
  return 0;
}

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

// §28.16: Table 28-9 — z→0 = d2, z→1 = d1.
TEST(GateNetDelays, ThreeDelayZTo0IsD2) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kZ, Val4::kV0), 20u);
}

TEST(GateNetDelays, ThreeDelayZTo1IsD1) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kZ, Val4::kV1), 10u);
}

// §28.16: "The strength of the input signal shall not affect the
//  propagation delay from an input to an output."
// (This is an architectural constraint, not directly testable via
//  the delay computation API — noted for completeness.)
// =============================================================
// §28.16.1: min:typ:max delays
// =============================================================
// §28.16.1: "The minimum, typical, and maximum values for each delay
//  shall be specified as expressions separated by colons."
// §28.16.1: "There shall be no required relation (e.g., min ≤ typ
//  ≤ max) between the expressions."
TEST(MinTypMaxDelays, SelectMin) {
  MinTypMax mtm{5, 10, 15};
  EXPECT_EQ(SelectMinTypMax(mtm, 0), 5u);
}

TEST(MinTypMaxDelays, SelectTyp) {
  MinTypMax mtm{5, 10, 15};
  EXPECT_EQ(SelectMinTypMax(mtm, 1), 10u);
}

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
