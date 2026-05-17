#include <gtest/gtest.h>

#include "parser/ast.h"

using namespace delta;

namespace {

TEST(ClockControlClassification, IncludesAllSixListedChecks) {
  EXPECT_TRUE(IsClockControlTimingCheck(TimingCheckKind::kSkew));
  EXPECT_TRUE(IsClockControlTimingCheck(TimingCheckKind::kTimeskew));
  EXPECT_TRUE(IsClockControlTimingCheck(TimingCheckKind::kFullskew));
  EXPECT_TRUE(IsClockControlTimingCheck(TimingCheckKind::kPeriod));
  EXPECT_TRUE(IsClockControlTimingCheck(TimingCheckKind::kWidth));
  EXPECT_TRUE(IsClockControlTimingCheck(TimingCheckKind::kNochange));
}

TEST(ClockControlClassification, ExcludesStabilityWindowChecks) {
  EXPECT_FALSE(IsClockControlTimingCheck(TimingCheckKind::kSetup));
  EXPECT_FALSE(IsClockControlTimingCheck(TimingCheckKind::kHold));
  EXPECT_FALSE(IsClockControlTimingCheck(TimingCheckKind::kSetuphold));
  EXPECT_FALSE(IsClockControlTimingCheck(TimingCheckKind::kRecovery));
  EXPECT_FALSE(IsClockControlTimingCheck(TimingCheckKind::kRemoval));
  EXPECT_FALSE(IsClockControlTimingCheck(TimingCheckKind::kRecrem));
}

}
