// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// 20. Exact integer delays pass through unchanged with any precision.
TEST(ParserClause03, Cl3_14_1_ExactIntegerPassThrough) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 5.0ns is exact at any precision → 5000ps.
  EXPECT_EQ(RealDelayToTicks(5.0, ts, TimeUnit::kPs), 5000u);
  // 3.0ns → 3000ps.
  EXPECT_EQ(RealDelayToTicks(3.0, ts, TimeUnit::kPs), 3000u);
}

}  // namespace
