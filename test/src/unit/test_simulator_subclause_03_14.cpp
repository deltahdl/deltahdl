#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_parse_314.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockSimulation, DelayToTicksFullRange) {
  TimeScale ts_s{TimeUnit::kS, 1, TimeUnit::kFs, 1};
  EXPECT_EQ(DelayToTicks(1, ts_s, TimeUnit::kFs), 1000000000000000ULL);

  TimeScale ts_fs{TimeUnit::kFs, 1, TimeUnit::kFs, 1};
  EXPECT_EQ(DelayToTicks(1, ts_fs, TimeUnit::kFs), 1u);
}

TEST(DesignBuildingBlockSimulation, PrecisionDeterminesDelayAccuracy) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kNs, 1};
  uint64_t coarse = DelayToTicks(1, ts, TimeUnit::kNs);
  uint64_t finer = DelayToTicks(1, ts, TimeUnit::kPs);
  uint64_t finest = DelayToTicks(1, ts, TimeUnit::kFs);
  EXPECT_GT(finer, coarse);
  EXPECT_GT(finest, finer);
  EXPECT_EQ(finer, coarse * 1000u);
  EXPECT_EQ(finest, coarse * 1000000u);
}

}  // namespace
