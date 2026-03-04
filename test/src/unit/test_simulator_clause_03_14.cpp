#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_parse_314.h"

using namespace delta;

namespace {

TEST(ParserClause03, Cl3_14_DelayToTicksFullRange) {

  TimeScale ts_s{TimeUnit::kS, 1, TimeUnit::kFs, 1};
  EXPECT_EQ(DelayToTicks(1, ts_s, TimeUnit::kFs), 1000000000000000ULL);

  TimeScale ts_fs{TimeUnit::kFs, 1, TimeUnit::kFs, 1};
  EXPECT_EQ(DelayToTicks(1, ts_fs, TimeUnit::kFs), 1u);
}

}
