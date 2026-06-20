#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_parse_314.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, DelayToTicksSameUnit) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kNs, 1};
  EXPECT_EQ(DelayToTicks(42, ts, TimeUnit::kNs), 42u);
}

// When the element's precision equals its time unit, a fractional delay is
// resolved to a whole number of time-unit ticks before it reaches simulation.
TEST(DesignBuildingBlockParsing, FractionalDelayRoundsToWholeUnit) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kNs, 1};
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kNs), 3u);
  EXPECT_EQ(RealDelayToTicks(2.3, ts, TimeUnit::kNs), 2u);
  EXPECT_EQ(RealDelayToTicks(2.5, ts, TimeUnit::kNs), 3u);
}

// One order of magnitude between unit and precision keeps a single fractional
// digit: with a 1 ns unit and 100 ps precision, 2.75 ns becomes 2.8 ns.
TEST(DesignBuildingBlockParsing, DelayRoundsToPrecisionStep) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);
}

// A delay is held to its own element's precision even when a finer precision
// exists elsewhere in the design (the shared, finer tick base here is ps).
TEST(DesignBuildingBlockParsing, DelayHeldToElementPrecision) {
  TimeScale coarse{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  TimeScale fine{TimeUnit::kNs, 1, TimeUnit::kPs, 1};
  EXPECT_EQ(RealDelayToTicks(2.756, coarse, TimeUnit::kPs), 2800u);
  EXPECT_EQ(RealDelayToTicks(2.756, fine, TimeUnit::kPs), 2756u);
  EXPECT_NE(RealDelayToTicks(2.756, coarse, TimeUnit::kPs),
            RealDelayToTicks(2.756, fine, TimeUnit::kPs));
}

// A zero delay resolves to zero ticks regardless of the rounding step.
TEST(DesignBuildingBlockParsing, ZeroDelayResolvesToZeroTicks) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  EXPECT_EQ(RealDelayToTicks(0.0, ts, TimeUnit::kPs), 0u);
}

}  // namespace
