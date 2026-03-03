// §3.14.1: Time value rounding

#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"

using namespace delta;

namespace {

// 21. Per-element accuracy: each design element rounds to its own precision,
// independent of finer precision specified elsewhere in the design.
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

}  // namespace
