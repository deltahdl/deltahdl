#include <gtest/gtest.h>

#include <cstdint>
#include <utility>
#include <vector>

#include "parser/ast_specify.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

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

TimingCheckEntry MakeSignedRecrem(int64_t recovery, int64_t removal) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kRecrem;
  tc.ref_signal = "clk";
  tc.data_signal = "rst";
  tc.negative_timing_check_enabled = true;
  tc.signed_limit = recovery;
  tc.signed_limit2 = removal;
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
  const auto kResult = AdjustNegativeTimingCheckLimit(1);
  EXPECT_EQ(kResult.limit, 1u);
  EXPECT_FALSE(kResult.warn);
}

TEST(AdjustNegativeTimingCheckLimit, ZeroClampsAndWarns) {
  const auto kResult = AdjustNegativeTimingCheckLimit(0);
  EXPECT_EQ(kResult.limit, 0u);
  EXPECT_TRUE(kResult.warn);
}

TEST(AdjustNegativeTimingCheckLimit, StrictlyNegativeClampsAndWarns) {
  const auto kResult = AdjustNegativeTimingCheckLimit(-3);
  EXPECT_EQ(kResult.limit, 0u);
  EXPECT_TRUE(kResult.warn);
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

TEST(NegativeTimingWindowCanYield, InvertedWindowCannotYield) {
  EXPECT_FALSE(NegativeTimingWindowCanYieldViolation(110, 100, 1));
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

TEST(LatchedNegativeTimingWindowValue, SettledBeforeWindowLatchesNewValue) {
  EXPECT_EQ(LatchedNegativeTimingWindowValue(105, 110, 105, 0xAA, 0xBB), 0xBBu);
  EXPECT_EQ(LatchedNegativeTimingWindowValue(105, 110, 100, 0xAA, 0xBB), 0xBBu);
}

TEST(LatchedNegativeTimingWindowValue, InteriorTransitionLatchesOldValue) {
  EXPECT_EQ(LatchedNegativeTimingWindowValue(105, 110, 107, 0xAA, 0xBB), 0xAAu);
}

TEST(LatchedNegativeTimingWindowValue, SettledAfterWindowLatchesOldValue) {
  EXPECT_EQ(LatchedNegativeTimingWindowValue(105, 110, 110, 0xAA, 0xBB), 0xAAu);
  EXPECT_EQ(LatchedNegativeTimingWindowValue(105, 110, 115, 0xAA, 0xBB), 0xAAu);
}

TEST(ImplicitDelayedSignalsRequired, NegativeAndNoExplicitCreatesImplicit) {
  EXPECT_TRUE(ImplicitDelayedSignalsRequired(true, false));
}

TEST(ImplicitDelayedSignalsRequired, ExplicitDeclaredSuppressesImplicit) {
  EXPECT_FALSE(ImplicitDelayedSignalsRequired(true, true));
}

TEST(ImplicitDelayedSignalsRequired, NoNegativeNeedsNoImplicit) {
  EXPECT_FALSE(ImplicitDelayedSignalsRequired(false, false));
  EXPECT_FALSE(ImplicitDelayedSignalsRequired(false, true));
}

TEST(EffectiveOutputDelayWithTimingCheckSignalDelay, DelayBelowPropUsesProp) {
  EXPECT_EQ(EffectiveOutputDelayWithTimingCheckSignalDelay(6, 4), 6u);
  EXPECT_EQ(EffectiveOutputDelayWithTimingCheckSignalDelay(6, 6), 6u);
}

TEST(EffectiveOutputDelayWithTimingCheckSignalDelay, DelayAbovePropOverrides) {
  EXPECT_EQ(EffectiveOutputDelayWithTimingCheckSignalDelay(6, 7), 7u);
}

TEST(ResolveDelayedSignals, SharedSignalGetsSingleImplicitCopy) {
  const std::vector<std::pair<std::string, std::string>> kRefs = {
      {"clk", ""}, {"data1", ""}, {"clk", ""}, {"data2", ""}};
  const auto kResolved = ResolveDelayedSignals(kRefs);
  ASSERT_EQ(kResolved.size(), 3u);
  EXPECT_EQ(kResolved[0].signal, "clk");
  EXPECT_FALSE(kResolved[0].is_explicit);
  EXPECT_EQ(kResolved[1].signal, "data1");
  EXPECT_EQ(kResolved[2].signal, "data2");
}

TEST(ResolveDelayedSignals, ExplicitInOneCheckIsUsedForAll) {
  const std::vector<std::pair<std::string, std::string>> kRefs = {
      {"clk", "del_clk"}, {"data1", "del_data1"}, {"clk", ""}, {"data2", ""}};
  const auto kResolved = ResolveDelayedSignals(kRefs);
  ASSERT_EQ(kResolved.size(), 3u);
  EXPECT_EQ(kResolved[0].signal, "clk");
  EXPECT_TRUE(kResolved[0].is_explicit);
  EXPECT_EQ(kResolved[0].delayed_name, "del_clk");
  EXPECT_EQ(kResolved[1].delayed_name, "del_data1");
  EXPECT_FALSE(kResolved[2].is_explicit);
}

TEST(ResolveDelayedSignals, ExplicitPromotesAnEarlierImplicitReference) {
  const std::vector<std::pair<std::string, std::string>> kRefs = {
      {"clk", ""}, {"clk", "del_clk"}};
  const auto kResolved = ResolveDelayedSignals(kRefs);
  ASSERT_EQ(kResolved.size(), 1u);
  EXPECT_TRUE(kResolved[0].is_explicit);
  EXPECT_EQ(kResolved[0].delayed_name, "del_clk");
}

TEST(NegativeTimingChecks, RuntimeInteriorYieldsViolation) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold(-5, 10));

  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 107));
}

TEST(NegativeTimingChecks, RuntimeLowerBoundaryIsExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold(-5, 10));

  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 105));
}

TEST(NegativeTimingChecks, RuntimeUpperBoundaryIsExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold(-5, 10));

  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 110));
}

TEST(NegativeTimingChecks, RuntimeChangeOutsideWindowIsNoViolation) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold(-5, 10));

  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 100));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 120));
}

TEST(NegativeTimingChecks, RuntimeNegativeHoldWindowInteriorYieldsViolation) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold(10, -5));

  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 92));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 90));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 95));
}

TEST(NegativeTimingChecks, RuntimeRecremRemovalBoundsTheEarlierSide) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedRecrem(-4, 14));

  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 200, "rst", 190));
}

TEST(NegativeTimingChecks, RuntimeRecremRecoveryDoesNotBoundTheEarlierSide) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedRecrem(-4, 14));

  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 200, "rst", 209));
}

TEST(NegativeTimingChecks, RuntimeSetupholdSetupBoundsTheEarlierSide) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold(-6, 22));

  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 300, "data", 314));
}

TEST(NegativeTimingChecks, RuntimeSetupholdHoldDoesNotBoundTheEarlierSide) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold(-6, 22));

  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 300, "data", 285));
}

}  // namespace
