// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// 17. Two orders of magnitude smaller: rounds to two decimal places.
TEST(ParserClause03, Cl3_14_1_TwoOrdersSmaller) {
  // 1ns unit, 10ps precision → 2 decimal places in ns.
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 10};
  // 2.756ns → 2.76ns = 2760ps.
  EXPECT_EQ(RealDelayToTicks(2.756, ts, TimeUnit::kPs), 2760u);
  // 2.754ns → 2.75ns = 2750ps.
  EXPECT_EQ(RealDelayToTicks(2.754, ts, TimeUnit::kPs), 2750u);
}

// 18. Three orders (full precision): no rounding needed.
TEST(ParserClause03, Cl3_14_1_ThreeOrdersNoRounding) {
  // 1ns unit, 1ps precision → 3 decimal places in ns.
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 1};
  // 2.756ns = 2756ps exactly, no rounding.
  EXPECT_EQ(RealDelayToTicks(2.756, ts, TimeUnit::kPs), 2756u);
}

// 19. Zero delay: rounds to zero regardless of precision.
TEST(ParserClause03, Cl3_14_1_ZeroDelay) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  EXPECT_EQ(RealDelayToTicks(0.0, ts, TimeUnit::kPs), 0u);
}

// 20. Exact integer delays pass through unchanged with any precision.
TEST(ParserClause03, Cl3_14_1_ExactIntegerPassThrough) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 5.0ns is exact at any precision → 5000ps.
  EXPECT_EQ(RealDelayToTicks(5.0, ts, TimeUnit::kPs), 5000u);
  // 3.0ns → 3000ps.
  EXPECT_EQ(RealDelayToTicks(3.0, ts, TimeUnit::kPs), 3000u);
}

}  // namespace
