#include <gtest/gtest.h>

#include "parser/ast.h"
#include "simulator/specify.h"

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
  // The clamp rule is "less than or equal to zero": a strictly negative
  // adjusted limit takes the "less than" branch, distinct from the zero
  // boundary above.
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
  // An upper bound below the lower bound is a degenerate (negative-width)
  // window and can never yield a violation, distinct from the equal-bounds
  // empty case.
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
  // Data reaches its new value at or before the window opens, so the new value
  // is stable across the excluded-endpoint interior and is the one latched.
  EXPECT_EQ(LatchedNegativeTimingWindowValue(105, 110, 105, 0xAA, 0xBB), 0xBBu);
  EXPECT_EQ(LatchedNegativeTimingWindowValue(105, 110, 100, 0xAA, 0xBB), 0xBBu);
}

TEST(LatchedNegativeTimingWindowValue, InteriorTransitionLatchesOldValue) {
  // A transition strictly inside the window is a violation (requirement (a));
  // per requirement (b)/Example 1 the stale old value is the one clocked in.
  EXPECT_EQ(LatchedNegativeTimingWindowValue(105, 110, 107, 0xAA, 0xBB), 0xAAu);
}

TEST(LatchedNegativeTimingWindowValue, SettledAfterWindowLatchesOldValue) {
  // Data does not change until at/after the window closes, so the old value is
  // stable across the interior and is latched.
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
  // The applied timing-check delay does not exceed the propagation delay, so
  // the output still changes at its nominal propagation delay.
  EXPECT_EQ(EffectiveOutputDelayWithTimingCheckSignalDelay(6, 4), 6u);
  EXPECT_EQ(EffectiveOutputDelayWithTimingCheckSignalDelay(6, 6), 6u);
}

TEST(EffectiveOutputDelayWithTimingCheckSignalDelay, DelayAbovePropOverrides) {
  // The applied delay exceeds the propagation delay, so the output transitions
  // when the delayed signal changes: the path delay becomes the applied delay.
  EXPECT_EQ(EffectiveOutputDelayWithTimingCheckSignalDelay(6, 7), 7u);
}

TEST(ResolveDelayedSignals, SharedSignalGetsSingleImplicitCopy) {
  // Example 2: CLK is referenced by two checks alongside DATA1 and DATA2. One
  // delayed copy is created per distinct signal -- CLK's single copy is shared
  // across both checks rather than duplicated.
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
  // Example 3: CLK and DATA1 are declared explicitly (del_clk, del_data1) in
  // the first check; the second check references CLK without declaring one. CLK
  // ends up with exactly one delayed signal -- the explicit del_clk -- not a
  // second implicit copy for the check that omitted it.
  const std::vector<std::pair<std::string, std::string>> kRefs = {
      {"clk", "del_clk"}, {"data1", "del_data1"}, {"clk", ""}, {"data2", ""}};
  const auto kResolved = ResolveDelayedSignals(kRefs);
  ASSERT_EQ(kResolved.size(), 3u);
  EXPECT_EQ(kResolved[0].signal, "clk");
  EXPECT_TRUE(kResolved[0].is_explicit);
  EXPECT_EQ(kResolved[0].delayed_name, "del_clk");
  EXPECT_EQ(kResolved[1].delayed_name, "del_data1");
  EXPECT_FALSE(kResolved[2].is_explicit);  // DATA2 stays implicit
}

TEST(ResolveDelayedSignals, ExplicitPromotesAnEarlierImplicitReference) {
  // Order-independence of the precedence rule: even when a signal is first seen
  // implicitly, a later check that declares it explicitly supplies the single
  // shared copy for both.
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

  // Negative setup shifts the window to (105, 110); a data change strictly
  // inside it triggers a violation per requirement (a).
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

  // Negative setup shifts the window to (105, 110). A data change well before
  // it opens or after it closes is genuinely outside -- not merely on an
  // endpoint -- and reports no violation.
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 100));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 120));
}

TEST(NegativeTimingChecks, RuntimeNegativeHoldWindowInteriorYieldsViolation) {
  SpecifyManager mgr;
  // Negative hold (Figure 31-5's other case): the window shifts to before the
  // reference edge -- here to (90, 95) -- rather than after it.
  mgr.AddTimingCheck(MakeSignedSetuphold(10, -5));

  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 92));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 90));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 95));
}

}  // namespace
