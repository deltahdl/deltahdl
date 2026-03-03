// §28.16.1: min:typ:max delays

#include <gtest/gtest.h>
#include <algorithm>
#include <cstdint>
#include <initializer_list>

// --- Local types for gate/net delays (§28.16) ---
enum class Val4 : uint8_t { kV0 = 0, kV1 = 1, kX = 2, kZ = 3 };

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

namespace {

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

}  // namespace
