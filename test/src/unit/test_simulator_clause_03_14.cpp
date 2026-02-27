// §3.14: Simulation time units and precision

#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_parse_314.h"

using namespace delta;

namespace {

// 11. DelayToTicks covers the full range from seconds to femtoseconds.
TEST(ParserClause03, Cl3_14_DelayToTicksFullRange) {
  // 1 second at fs precision = 10^15 ticks.
  TimeScale ts_s{TimeUnit::kS, 1, TimeUnit::kFs, 1};
  EXPECT_EQ(DelayToTicks(1, ts_s, TimeUnit::kFs), 1000000000000000ULL);
  // 1 fs at fs precision = 1 tick.
  TimeScale ts_fs{TimeUnit::kFs, 1, TimeUnit::kFs, 1};
  EXPECT_EQ(DelayToTicks(1, ts_fs, TimeUnit::kFs), 1u);
}

}  // namespace
