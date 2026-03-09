#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_parse_314.h"

using namespace delta;

namespace {

TEST(ParserClause03, Cl3_14_DelayToTicksSameUnit) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kNs, 1};
  EXPECT_EQ(DelayToTicks(42, ts, TimeUnit::kNs), 42u);
}

}
