#include <gtest/gtest.h>

#include "common/types.h"

using namespace delta;

// =============================================================================
// LRM §3.14.1 — Time value rounding
// =============================================================================

// 14. Same precision as unit: delay values rounded to whole numbers.
// "If the precision is the same as the time units, then delay values are
// rounded off to whole numbers (integers)."
TEST(ParserClause03, Cl3_14_1_SamePrecisionRoundsToInteger) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kNs, 1};
  // 2.75ns with 1ns precision rounds to 3ns = 3 ticks at ns.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kNs), 3u);
  // 2.3ns rounds to 2ns.
  EXPECT_EQ(RealDelayToTicks(2.3, ts, TimeUnit::kNs), 2u);
  // 2.5ns rounds to 3ns (round half away from zero).
  EXPECT_EQ(RealDelayToTicks(2.5, ts, TimeUnit::kNs), 3u);
}

// 15. One order of magnitude smaller: rounds to one decimal place.
// "If the precision is one order of magnitude smaller than the time units,
// then delay values are rounded off to one decimal place."
TEST(ParserClause03, Cl3_14_1_OneOrderSmallerRoundsToOneDecimal) {
  // 1ns unit, 100ps precision → 1 decimal place in ns.
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 2.75ns → 2.8ns = 2800ps = 2800 ticks at ps.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);
  // 2.73ns → 2.7ns = 2700ps.
  EXPECT_EQ(RealDelayToTicks(2.73, ts, TimeUnit::kPs), 2700u);
}

// 16. LRM example: "if the time unit specified is 1ns and the precision
// is 100ps, then ... a delay of 2.75ns would be rounded off to 2.8ns."
TEST(ParserClause03, Cl3_14_1_LrmExample_2_75ns) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 2.75ns rounded to nearest 100ps = 2.8ns = 2800 ticks at ps.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);
  // Verify in ns-tick form: at ns precision, 2800ps = 2.8ns ≈ 3 ticks.
  // But at ps global precision the value is 2800.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);
}

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

// 21. Per-element accuracy: "The time values in a design element are
// accurate to within the unit of time precision specified for that
// design element, even if there is a smaller time precision specified
// elsewhere in the design."
TEST(ParserClause03, Cl3_14_1_PerElementAccuracy) {
  // Element A: 1ns / 100ps — rounds to 0.1ns steps.
  TimeScale ts_a{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // Element B: 1ns / 1ps — rounds to 0.001ns steps.
  TimeScale ts_b{TimeUnit::kNs, 1, TimeUnit::kPs, 1};
  // Same delay 2.756ns produces different results per element.
  // Element A: 2.756 → 2.8ns = 2800ps.
  EXPECT_EQ(RealDelayToTicks(2.756, ts_a, TimeUnit::kPs), 2800u);
  // Element B: 2.756 → 2.756ns = 2756ps (no rounding at 1ps).
  EXPECT_EQ(RealDelayToTicks(2.756, ts_b, TimeUnit::kPs), 2756u);
  // The two results differ because each element uses its own precision.
  EXPECT_NE(RealDelayToTicks(2.756, ts_a, TimeUnit::kPs),
            RealDelayToTicks(2.756, ts_b, TimeUnit::kPs));
}

// 22. Magnitude affects rounding: 10ns unit with 1ns precision.
TEST(ParserClause03, Cl3_14_1_MagnitudeRounding) {
  // 10ns unit, 1ns precision → delays in multiples of 10ns, rounded to 1ns.
  TimeScale ts{TimeUnit::kNs, 10, TimeUnit::kNs, 1};
  // delay=2.75 means 2.75 * 10ns = 27.5ns → rounds to 28ns = 28 ticks.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kNs), 28u);
  // delay=1.0 means 10ns = 10 ticks.
  EXPECT_EQ(RealDelayToTicks(1.0, ts, TimeUnit::kNs), 10u);
}

// 23. Rounding with global precision finer than element precision.
// Global precision = fs, element precision = 100ps.
// Rounding still occurs at element's precision step.
TEST(ParserClause03, Cl3_14_1_FinerGlobalPrecision) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 2.75ns at fs global precision:
  // raw ticks = 2.75 * 10^6 = 2750000 fs.
  // precision step = 100 * 10^3 = 100000 fs.
  // 2750000 / 100000 = 27.5 → round to 28 → 28 * 100000 = 2800000 fs.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kFs), 2800000u);
}
