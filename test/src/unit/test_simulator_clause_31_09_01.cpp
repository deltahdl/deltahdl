#include "parser/ast.h"
#include "simulator/specify.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

// Build a $setuphold entry running in §31.9 signed-limit mode so the
// rule (a) endpoint-exclusion behaviour can be observed through the
// actual runtime check rather than against a bare helper.
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

// §31.9.1: the nine window-based and single-signal kinds must consume
// the delayed versions of their data and reference signals so the
// notifier fires at the proper moment.
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

// §31.9.1: the three event-order kinds must not consume the delayed
// versions, because delaying their inputs can reverse the observed
// transition order and fire the notifier at the wrong time.
TEST(NegativeTimingCheckDelayedSignals, EventOrderKindsDoNotUseDelayedSignals) {
  EXPECT_FALSE(TimingCheckUsesDelayedSignals(TimingCheckKind::kSkew));
  EXPECT_FALSE(TimingCheckUsesDelayedSignals(TimingCheckKind::kFullskew));
  EXPECT_FALSE(TimingCheckUsesDelayedSignals(TimingCheckKind::kTimeskew));
}

// §31.9.1: a strictly-positive adjusted limit survives the clamp
// unchanged and carries no warning obligation.
TEST(AdjustNegativeTimingCheckLimit, PositivePassesThroughWithoutWarning) {
  const auto result = AdjustNegativeTimingCheckLimit(7);
  EXPECT_EQ(result.limit, 7u);
  EXPECT_FALSE(result.warn);
}

// §31.9.1: the smallest possible positive adjusted limit sits one
// tick above the clamp boundary and must pass through unchanged.
// This pins the boundary explicitly so the rule's "strictly greater
// than zero" side cannot drift to "greater than or equal" without
// being caught.
TEST(AdjustNegativeTimingCheckLimit, SmallestPositivePassesThrough) {
  const auto result = AdjustNegativeTimingCheckLimit(1);
  EXPECT_EQ(result.limit, 1u);
  EXPECT_FALSE(result.warn);
}

// §31.9.1: the LRM's "≤ 0" rule folds the exactly-zero case in with
// the negative case — both clamp to zero and must warn.
TEST(AdjustNegativeTimingCheckLimit, ZeroClampsAndWarns) {
  const auto result = AdjustNegativeTimingCheckLimit(0);
  EXPECT_EQ(result.limit, 0u);
  EXPECT_TRUE(result.warn);
}

// §31.9.1: a negative adjusted limit clamps to zero and warns.
TEST(AdjustNegativeTimingCheckLimit, NegativeClampsAndWarns) {
  const auto result = AdjustNegativeTimingCheckLimit(-4);
  EXPECT_EQ(result.limit, 0u);
  EXPECT_TRUE(result.warn);
}

// §31.9.1 rule (a): an open interval spanning at least two ticks of
// simulation precision can witness an interior transition.
TEST(NegativeTimingWindowCanYield, WidthAtLeastTwoYields) {
  EXPECT_TRUE(NegativeTimingWindowCanYieldViolation(100, 102, 1));
}

// §31.9.1 rule (a): a one-tick-wide open interval has no strictly
// interior sample point and cannot yield a violation.
TEST(NegativeTimingWindowCanYield, WidthOneCannotYield) {
  EXPECT_FALSE(NegativeTimingWindowCanYieldViolation(100, 101, 1));
}

// §31.9.1 rule (a): an empty interval cannot yield a violation.
TEST(NegativeTimingWindowCanYield, EmptyCannotYield) {
  EXPECT_FALSE(NegativeTimingWindowCanYieldViolation(100, 100, 1));
}

// §31.9.1 rule (a): the "two units of simulation precision" floor
// scales with the caller-supplied precision — at ten ticks per unit,
// the interval must span twenty ticks.
TEST(NegativeTimingWindowCanYield, LargerPrecisionScalesThreshold) {
  EXPECT_FALSE(NegativeTimingWindowCanYieldViolation(0, 19, 10));
  EXPECT_TRUE(NegativeTimingWindowCanYieldViolation(0, 20, 10));
}

// §31.9.1 resolution procedure: an empty limit vector has nothing to
// rewrite, so the helper returns false without touching it.
TEST(ZeroSmallestNegativeTimingLimit, EmptyVectorReturnsFalse) {
  std::vector<int64_t> limits;
  EXPECT_FALSE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_TRUE(limits.empty());
}

// §31.9.1 resolution procedure: a vector with no negatives represents
// a consistent state, so the helper signals "nothing to do" and
// leaves the values alone.
TEST(ZeroSmallestNegativeTimingLimit, AllNonNegativeReturnsFalse) {
  std::vector<int64_t> limits = {0, 3, 10};
  EXPECT_FALSE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_EQ(limits, (std::vector<int64_t>{0, 3, 10}));
}

// §31.9.1 resolution procedure: a single negative is the only
// candidate, so it is zeroed.
TEST(ZeroSmallestNegativeTimingLimit, SingleNegativeIsZeroed) {
  std::vector<int64_t> limits = {5, -3, 7};
  EXPECT_TRUE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_EQ(limits, (std::vector<int64_t>{5, 0, 7}));
}

// §31.9.1 resolution procedure: among several negatives the one
// closest to zero (smallest in magnitude) is the conservative
// choice and must be the one rewritten.
TEST(ZeroSmallestNegativeTimingLimit, NearestToZeroIsZeroed) {
  std::vector<int64_t> limits = {-10, -1, -5};
  EXPECT_TRUE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_EQ(limits, (std::vector<int64_t>{-10, 0, -5}));
}

// §31.9.1 resolution procedure: when two negatives share the smallest
// magnitude the earliest position is rewritten for determinism.
TEST(ZeroSmallestNegativeTimingLimit, TieGoesToEarliest) {
  std::vector<int64_t> limits = {-3, -1, -1, -2};
  EXPECT_TRUE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_EQ(limits, (std::vector<int64_t>{-3, 0, -1, -2}));
}

// §31.9.1 resolution procedure: positive and zero entries are
// ignored — only negatives are candidates.
TEST(ZeroSmallestNegativeTimingLimit, PositivesAndZerosIgnored) {
  std::vector<int64_t> limits = {0, -4, 100, -2, 0};
  EXPECT_TRUE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_EQ(limits, (std::vector<int64_t>{0, -4, 100, 0, 0}));
}

// §31.9.1 resolution procedure: repeated invocation eventually
// zeros every negative and leaves the vector in a solvable state —
// the termination guarantee the LRM calls out explicitly.
TEST(ZeroSmallestNegativeTimingLimit, RepeatedApplicationTerminates) {
  std::vector<int64_t> limits = {-5, -1, -10};
  EXPECT_TRUE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_TRUE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_TRUE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_FALSE(ZeroSmallestNegativeTimingLimit(limits));
  EXPECT_EQ(limits, (std::vector<int64_t>{0, 0, 0}));
}

// §31.9.1 rule (a) observed through the runtime: the lower boundary
// of a shifted-after window is excluded from the violation region, so
// a data event landing exactly on it must not violate.
TEST(NegativeTimingChecks, RuntimeLowerBoundaryIsExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold(/*setup=*/-5, /*hold=*/10));
  // Left boundary is ref - setup = 105.
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 105));
}

// §31.9.1 rule (a) observed through the runtime: the upper boundary
// is also excluded.
TEST(NegativeTimingChecks, RuntimeUpperBoundaryIsExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold(/*setup=*/-5, /*hold=*/10));
  // Right boundary is ref + hold = 110.
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 110));
}

}  // namespace
