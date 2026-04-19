#include <gtest/gtest.h>

#include "parser/ast.h"

using namespace delta;

namespace {

// §31.4 lists exactly six timing checks ($skew, $timeskew, $fullskew, $period,
// $width, $nochange) as the clock/control-signal group that shares the generic
// elapsed-time-vs-limit procedure.
TEST(ClockControlClassification, IncludesAllSixListedChecks) {
  EXPECT_TRUE(IsClockControlTimingCheck(TimingCheckKind::kSkew));
  EXPECT_TRUE(IsClockControlTimingCheck(TimingCheckKind::kTimeskew));
  EXPECT_TRUE(IsClockControlTimingCheck(TimingCheckKind::kFullskew));
  EXPECT_TRUE(IsClockControlTimingCheck(TimingCheckKind::kPeriod));
  EXPECT_TRUE(IsClockControlTimingCheck(TimingCheckKind::kWidth));
  EXPECT_TRUE(IsClockControlTimingCheck(TimingCheckKind::kNochange));
}

// The other six timing-check kinds belong to §31.3's stability-window group
// and must not be classified as clock/control-signal checks.
TEST(ClockControlClassification, ExcludesStabilityWindowChecks) {
  EXPECT_FALSE(IsClockControlTimingCheck(TimingCheckKind::kSetup));
  EXPECT_FALSE(IsClockControlTimingCheck(TimingCheckKind::kHold));
  EXPECT_FALSE(IsClockControlTimingCheck(TimingCheckKind::kSetuphold));
  EXPECT_FALSE(IsClockControlTimingCheck(TimingCheckKind::kRecovery));
  EXPECT_FALSE(IsClockControlTimingCheck(TimingCheckKind::kRemoval));
  EXPECT_FALSE(IsClockControlTimingCheck(TimingCheckKind::kRecrem));
}

}  // namespace
