#include "common/types.h"
#include "parser/ast.h"
#include "simulator/specify.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

// §31.8: $width and $period are the two single-signal timing checks
// the LRM names — their data event is derived from the same reference
// signal, so per-bit expansion fans out only across the reference width.
TEST(VectorSignalsInTimingChecks, WidthAndPeriodClassifyAsSingleSignal) {
  EXPECT_TRUE(IsSingleSignalTimingCheck(TimingCheckKind::kWidth));
  EXPECT_TRUE(IsSingleSignalTimingCheck(TimingCheckKind::kPeriod));
}

// §31.8: every other timing-check kind names two distinct signals,
// putting them on the two-signal side of the classifier where per-bit
// expansion fans out across the cross-product of the two widths.
TEST(VectorSignalsInTimingChecks, TwoSignalChecksClassifyAsTwoSignal) {
  EXPECT_FALSE(IsSingleSignalTimingCheck(TimingCheckKind::kSetup));
  EXPECT_FALSE(IsSingleSignalTimingCheck(TimingCheckKind::kHold));
  EXPECT_FALSE(IsSingleSignalTimingCheck(TimingCheckKind::kSetuphold));
  EXPECT_FALSE(IsSingleSignalTimingCheck(TimingCheckKind::kRecovery));
  EXPECT_FALSE(IsSingleSignalTimingCheck(TimingCheckKind::kRemoval));
  EXPECT_FALSE(IsSingleSignalTimingCheck(TimingCheckKind::kRecrem));
  EXPECT_FALSE(IsSingleSignalTimingCheck(TimingCheckKind::kSkew));
  EXPECT_FALSE(IsSingleSignalTimingCheck(TimingCheckKind::kTimeskew));
  EXPECT_FALSE(IsSingleSignalTimingCheck(TimingCheckKind::kFullskew));
  EXPECT_FALSE(IsSingleSignalTimingCheck(TimingCheckKind::kNochange));
}

// §31.8 default: a vector signal participates as a unified signal and
// the invocation produces exactly one timing check, regardless of the
// terminal widths. The LRM example with an 8-bit DAT and a scalar CLK
// witnesses this — six bit transitions still report a single violation.
// Every kind the LRM enumerates must collapse to a single check in this
// mode, so every TimingCheckKind value is exercised.
TEST(VectorSignalsInTimingChecks, SingleModeAlwaysYieldsOneCheck) {
  const TimingCheckKind kinds[] = {
      TimingCheckKind::kSetup,    TimingCheckKind::kHold,
      TimingCheckKind::kSetuphold, TimingCheckKind::kRecovery,
      TimingCheckKind::kRemoval,  TimingCheckKind::kRecrem,
      TimingCheckKind::kSkew,     TimingCheckKind::kTimeskew,
      TimingCheckKind::kFullskew, TimingCheckKind::kNochange,
      TimingCheckKind::kWidth,    TimingCheckKind::kPeriod,
  };
  for (auto k : kinds) {
    EXPECT_EQ(TimingCheckExpandedCount(k, 8, 8,
                                       TimingCheckVectorMode::kSingle),
              1u);
  }
}

// §31.8 (optional expansion): "For timing checks with only a single
// signal, such as $period or $width, a vector of width N results in N
// unique timing checks." The data-side argument is irrelevant for
// single-signal kinds and must not contribute to the count.
TEST(VectorSignalsInTimingChecks, PerBitModeWidthExpandsToReferenceWidth) {
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kWidth, 8, 0,
                                     TimingCheckVectorMode::kPerBit),
            8u);
  // Period vector of width 4 expands to four unique checks.
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kPeriod, 4, 1,
                                     TimingCheckVectorMode::kPerBit),
            4u);
  // The data-side argument is ignored for single-signal kinds, so a
  // nonsense data width does not change the count.
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kWidth, 3, 99,
                                     TimingCheckVectorMode::kPerBit),
            3u);
}

// §31.8 (optional expansion): "For timing checks with two signals,
// such as $setup, $hold, ..., where M and N are the widths of the
// signals, the result is M*N unique timing checks." With expansion
// enabled the LRM example — an 8-bit DAT and a scalar CLK — expands
// to 8 * 1 = 8 unique checks (six of which witness violations on the
// stated transition).
TEST(VectorSignalsInTimingChecks, PerBitModeTwoSignalExpandsToCrossProduct) {
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kSetup, 8, 1,
                                     TimingCheckVectorMode::kPerBit),
            8u);
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kSetup, 4, 4,
                                     TimingCheckVectorMode::kPerBit),
            16u);
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kHold, 2, 8,
                                     TimingCheckVectorMode::kPerBit),
            16u);
  // $nochange is the last two-signal kind the LRM enumerates: it must
  // expand on the cross-product side too.
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kNochange, 8, 8,
                                     TimingCheckVectorMode::kPerBit),
            64u);
}

// §31.8 (optional expansion): the LRM names ten two-signal checks —
// $setup, $hold, $setuphold, $recovery, $removal, $recrem, $skew,
// $timeskew, $fullskew, $nochange — that must all fan out across the
// cross-product of the two terminal widths. Sweep every named kind so
// no enumeration value is implicitly exempt from the rule.
TEST(VectorSignalsInTimingChecks, PerBitModeAllTwoSignalKindsExpand) {
  const TimingCheckKind two_signal_kinds[] = {
      TimingCheckKind::kSetup,    TimingCheckKind::kHold,
      TimingCheckKind::kSetuphold, TimingCheckKind::kRecovery,
      TimingCheckKind::kRemoval,  TimingCheckKind::kRecrem,
      TimingCheckKind::kSkew,     TimingCheckKind::kTimeskew,
      TimingCheckKind::kFullskew, TimingCheckKind::kNochange,
  };
  for (auto k : two_signal_kinds) {
    EXPECT_EQ(TimingCheckExpandedCount(k, 3, 5,
                                       TimingCheckVectorMode::kPerBit),
              15u);
  }
}

// §31.8 worked example: "DAT is an 8-bit data terminal" tested against
// a scalar CLK. The LRM observes that under default semantics one
// invocation reports a single violation regardless of how many bit
// transitions occur, while the optional per-bit mode produces eight
// unique checks (six of which witness the stated violation). The
// expansion math must reflect both outcomes for that exact shape.
TEST(VectorSignalsInTimingChecks, LrmEightBitDataAgainstScalarClock) {
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kSetup, 1, 8,
                                     TimingCheckVectorMode::kSingle),
            1u);
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kSetup, 1, 8,
                                     TimingCheckVectorMode::kPerBit),
            8u);
}

// §31.8: a width that elaboration could not determine should not
// produce a spurious expansion count. A zero argument collapses the
// product to zero so callers see an unambiguous "no expansion".
TEST(VectorSignalsInTimingChecks, PerBitModeZeroWidthCollapsesToZero) {
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kSetup, 0, 8,
                                     TimingCheckVectorMode::kPerBit),
            0u);
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kSetup, 8, 0,
                                     TimingCheckVectorMode::kPerBit),
            0u);
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kWidth, 0, 1,
                                     TimingCheckVectorMode::kPerBit),
            0u);
}

// §31.8 default: scalar invocations witness the trivial case that the
// helper still reports exactly one check, mirroring how a scalar
// terminal behaves identically in either mode.
TEST(VectorSignalsInTimingChecks, ScalarInvocationsYieldOneCheckInBothModes) {
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kSetup, 1, 1,
                                     TimingCheckVectorMode::kSingle),
            1u);
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kSetup, 1, 1,
                                     TimingCheckVectorMode::kPerBit),
            1u);
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kWidth, 1, 0,
                                     TimingCheckVectorMode::kPerBit),
            1u);
}

}  // namespace
