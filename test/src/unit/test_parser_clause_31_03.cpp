#include <gtest/gtest.h>

#include "parser/ast.h"

using namespace delta;

namespace {

// §31.3 classifies exactly these six timing checks as the stability-window
// group. Each is listed by the subclause alongside the generic three-step
// procedure (define window, check data transition, report violation).
TEST(StabilityWindowClassification, IncludesAllSixListedChecks) {
  EXPECT_TRUE(IsStabilityWindowTimingCheck(TimingCheckKind::kSetup));
  EXPECT_TRUE(IsStabilityWindowTimingCheck(TimingCheckKind::kHold));
  EXPECT_TRUE(IsStabilityWindowTimingCheck(TimingCheckKind::kSetuphold));
  EXPECT_TRUE(IsStabilityWindowTimingCheck(TimingCheckKind::kRecovery));
  EXPECT_TRUE(IsStabilityWindowTimingCheck(TimingCheckKind::kRemoval));
  EXPECT_TRUE(IsStabilityWindowTimingCheck(TimingCheckKind::kRecrem));
}

// The other six timing-check kinds belong to §31.4 (event-based group) and
// must not be classified as stability-window checks.
TEST(StabilityWindowClassification, ExcludesEventBasedChecks) {
  EXPECT_FALSE(IsStabilityWindowTimingCheck(TimingCheckKind::kSkew));
  EXPECT_FALSE(IsStabilityWindowTimingCheck(TimingCheckKind::kTimeskew));
  EXPECT_FALSE(IsStabilityWindowTimingCheck(TimingCheckKind::kFullskew));
  EXPECT_FALSE(IsStabilityWindowTimingCheck(TimingCheckKind::kWidth));
  EXPECT_FALSE(IsStabilityWindowTimingCheck(TimingCheckKind::kPeriod));
  EXPECT_FALSE(IsStabilityWindowTimingCheck(TimingCheckKind::kNochange));
}

}  // namespace
