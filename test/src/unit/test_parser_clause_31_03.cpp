#include <gtest/gtest.h>

#include "parser/ast.h"

using namespace delta;

namespace {

TEST(StabilityWindowClassification, IncludesAllSixListedChecks) {
  EXPECT_TRUE(IsStabilityWindowTimingCheck(TimingCheckKind::kSetup));
  EXPECT_TRUE(IsStabilityWindowTimingCheck(TimingCheckKind::kHold));
  EXPECT_TRUE(IsStabilityWindowTimingCheck(TimingCheckKind::kSetuphold));
  EXPECT_TRUE(IsStabilityWindowTimingCheck(TimingCheckKind::kRecovery));
  EXPECT_TRUE(IsStabilityWindowTimingCheck(TimingCheckKind::kRemoval));
  EXPECT_TRUE(IsStabilityWindowTimingCheck(TimingCheckKind::kRecrem));
}

TEST(StabilityWindowClassification, ExcludesEventBasedChecks) {
  EXPECT_FALSE(IsStabilityWindowTimingCheck(TimingCheckKind::kSkew));
  EXPECT_FALSE(IsStabilityWindowTimingCheck(TimingCheckKind::kTimeskew));
  EXPECT_FALSE(IsStabilityWindowTimingCheck(TimingCheckKind::kFullskew));
  EXPECT_FALSE(IsStabilityWindowTimingCheck(TimingCheckKind::kWidth));
  EXPECT_FALSE(IsStabilityWindowTimingCheck(TimingCheckKind::kPeriod));
  EXPECT_FALSE(IsStabilityWindowTimingCheck(TimingCheckKind::kNochange));
}

}
