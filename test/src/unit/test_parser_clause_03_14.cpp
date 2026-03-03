// §3.14: Simulation time units and precision

#include "fixture_parser.h"

using namespace delta;

namespace {

// 1. TimeUnit enum: six values with correct power-of-10 exponents
// (s=0, ms=-3, us=-6, ns=-9, ps=-12, fs=-15).
TEST(ParserClause03, Cl3_14_TimeUnitEnumValues) {
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kS), 0);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kMs), -3);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kUs), -6);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kNs), -9);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kPs), -12);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kFs), -15);
}

}  // namespace
