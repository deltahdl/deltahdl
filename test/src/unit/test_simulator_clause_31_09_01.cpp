#include "parser/ast.h"
#include "simulator/specify.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

TimingCheckEntry MakeSignedSetuphold(int64_t setup, int64_t hold) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetuphold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.negative_timing_check_enabled = true;
  tc.signed_limit = setup;
  tc.signed_limit2 = hold;
  return tc;
}

TEST(NegativeTimingCheckDelayedSignals, WindowKindsUseDelayedSignals) {
  EXPECT_TRUE(TimingCheckUsesDelayedSignals(TimingCheckKind::kSetup));
  EXPECT_TRUE(TimingCheckUsesDelayedSignals(TimingCheckKind::kHold));
  EXPECT_TRUE(TimingCheckUsesDelayedSignals(TimingCheckKind::kSetuphold));
  EXPECT_TRUE(TimingCheckUsesDelayedSignals(TimingCheckKind::kRecovery));
  EXPECT_TRUE(TimingCheckUsesDelayedSignals(TimingCheckKind::kRemoval));
  EXPECT_TRUE(TimingCheckUsesDelayedSignals(TimingCheckKind::kRecrem));
  EXPECT_TRUE(TimingCheckUsesDelayedSignals(TimingCheckKind::kWidth));
  EXPECT_TRUE(TimingCheckUsesDelayedSignals(TimingCheckKind::kPeriod));
  EXPECT_TRUE(TimingCheckUsesDelayedSignals(TimingCheckKind::kNochange));
}

TEST(NegativeTimingCheckDelayedSignals, EventOrderKindsDoNotUseDelayedSignals) {
  EXPECT_FALSE(TimingCheckUsesDelayedSignals(TimingCheckKind::kSkew));
  EXPECT_FALSE(TimingCheckUsesDelayedSignals(TimingCheckKind::kFullskew));
  EXPECT_FALSE(TimingCheckUsesDelayedSignals(TimingCheckKind::kTimeskew));
}

TEST(AdjustNegativeTimingCheckLimit, SmallestPositivePassesThrough) {
  const auto result = AdjustNegativeTimingCheckLimit(1);
  EXPECT_EQ(result.limit, 1u);
  EXPECT_FALSE(result.warn);
}

TEST(AdjustNegativeTimingCheckLimit, ZeroClampsAndWarns) {
  const auto result = AdjustNegativeTimingCheckLimit(0);
  EXPECT_EQ(result.limit, 0u);
  EXPECT_TRUE(result.warn);
}

TEST(NegativeTimingWindowCanYield, WidthAtLeastTwoYields) {
  EXPECT_TRUE(NegativeTimingWindowCanYieldViolation(100, 102, 1));
}

TEST(NegativeTimingWindowCanYield, WidthOneCannotYield) {
  EXPECT_FALSE(NegativeTimingWindowCanYieldViolation(100, 101, 1));
}

TEST(NegativeTimingWindowCanYield, EmptyCannotYield) {
  EXPECT_FALSE(NegativeTimingWindowCanYieldViolation(100, 100, 1));
}

TEST(NegativeTimingWindowCanYield, LargerPrecisionScalesThreshold) {
  EXPECT_FALSE(NegativeTimingWindowCanYieldViolation(0, 19, 10));
  EXPECT_TRUE(NegativeTimingWindowCanYieldViolation(0, 20, 10));
}

TEST(ZeroSmallestNegativeTimingLimit, EmptyVectorReturnsFalse) {
  std::vector<int64_t> limits;
  EXPECT_FALSE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_TRUE(limits.empty());
}

TEST(ZeroSmallestNegativeTimingLimit, AllNonNegativeReturnsFalse) {
  std::vector<int64_t> limits = {0, 3, 10};
  EXPECT_FALSE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_EQ(limits, (std::vector<int64_t>{0, 3, 10}));
}

TEST(ZeroSmallestNegativeTimingLimit, SingleNegativeIsZeroed) {
  std::vector<int64_t> limits = {5, -3, 7};
  EXPECT_TRUE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_EQ(limits, (std::vector<int64_t>{5, 0, 7}));
}

TEST(ZeroSmallestNegativeTimingLimit, NearestToZeroIsZeroed) {
  std::vector<int64_t> limits = {-10, -1, -5};
  EXPECT_TRUE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_EQ(limits, (std::vector<int64_t>{-10, 0, -5}));
}

TEST(ZeroSmallestNegativeTimingLimit, TieGoesToEarliest) {
  std::vector<int64_t> limits = {-3, -1, -1, -2};
  EXPECT_TRUE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_EQ(limits, (std::vector<int64_t>{-3, 0, -1, -2}));
}

TEST(ZeroSmallestNegativeTimingLimit, RepeatedApplicationTerminates) {
  std::vector<int64_t> limits = {-5, -1, -10};
  EXPECT_TRUE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_TRUE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_TRUE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_FALSE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_EQ(limits, (std::vector<int64_t>{0, 0, 0}));
}

TEST(NegativeTimingChecks, RuntimeInteriorYieldsViolation) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold( -5, 10));

  // Negative setup shifts the window to (105, 110); a data change strictly
  // inside it triggers a violation per requirement (a).
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 107));
}

TEST(NegativeTimingChecks, RuntimeLowerBoundaryIsExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold( -5, 10));

  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 105));
}

TEST(NegativeTimingChecks, RuntimeUpperBoundaryIsExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold( -5, 10));

  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 110));
}

}
