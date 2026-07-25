#include <gtest/gtest.h>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

TEST(VectorSignalsInTimingChecks, WidthAndPeriodClassifyAsSingleSignal) {
  EXPECT_TRUE(IsSingleSignalTimingCheck(TimingCheckKind::kWidth));
  EXPECT_TRUE(IsSingleSignalTimingCheck(TimingCheckKind::kPeriod));
}

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

TEST(VectorSignalsInTimingChecks, SingleModeAlwaysYieldsOneCheck) {
  const TimingCheckKind kKinds[] = {
      TimingCheckKind::kSetup,     TimingCheckKind::kHold,
      TimingCheckKind::kSetuphold, TimingCheckKind::kRecovery,
      TimingCheckKind::kRemoval,   TimingCheckKind::kRecrem,
      TimingCheckKind::kSkew,      TimingCheckKind::kTimeskew,
      TimingCheckKind::kFullskew,  TimingCheckKind::kNochange,
      TimingCheckKind::kWidth,     TimingCheckKind::kPeriod,
  };
  for (auto k : kKinds) {
    EXPECT_EQ(TimingCheckExpandedCount(k, 8, 8, TimingCheckVectorMode::kSingle),
              1u);
  }
}

TEST(VectorSignalsInTimingChecks, PerBitModeWidthExpandsToReferenceWidth) {
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kWidth, 8, 0,
                                     TimingCheckVectorMode::kPerBit),
            8u);

  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kPeriod, 4, 1,
                                     TimingCheckVectorMode::kPerBit),
            4u);

  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kWidth, 3, 99,
                                     TimingCheckVectorMode::kPerBit),
            3u);
}

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

  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kNochange, 8, 8,
                                     TimingCheckVectorMode::kPerBit),
            64u);
}

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

// §31.8, S1/S2: the LRM's DFF example. $setup(DAT, posedge CLK, 10) with DAT an
// 8-bit vector data operand. When several bits of DAT change at the same time,
// the runtime treats that as a single transition of the vector -- one event fed
// to the $setup machinery -- so the check reports exactly one violation rather
// than one per changed bit. This drives the real §31.3.1 setup-violation path
// (CheckSetupViolation) that the "shall still only report a single timing
// violation" statement governs, using the LRM's own numbers: DAT transitions at
// time 100, CLK at 105, limit 10, so the data change lands strictly inside the
// (95,105) setup window.
TEST(VectorSignalsInTimingChecks, VectorTransitionReportsSingleSetupViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetup;
  tc.ref_signal = "CLK";
  tc.data_signal = "DAT";
  tc.limit = 10;
  mgr.AddTimingCheck(tc);

  // The multi-bit DAT change at time 100 is a single vector transition, so the
  // setup check against the CLK edge at 105 yields one violation.
  EXPECT_TRUE(mgr.CheckSetupViolation("CLK", 105, "DAT", 100));

  // And in the default (single) mode the 8-bit-vs-scalar invocation is a single
  // timing check, not eight -- the count side of the same rule.
  EXPECT_EQ(
      TimingCheckExpandedCount(TimingCheckKind::kSetup, /*ref=*/1,
                               /*data=*/8, TimingCheckVectorMode::kSingle),
      1u);
}

// §31.8, D4 (per-bit expansion option): the LRM's own DFF example. With the
// option enabled, $setup(DAT[7:0], posedge CLK) expands into M*N = 1*8 = 8
// single-bit checks, but the event reports only six violations because DAT
// changes in six of its eight bit positions ('b00101110 -> 'b01010011). This
// distinguishes the count of checks created (8) from the count of violations
// reported (6) -- the latter tracks the bits that actually transitioned.
TEST(VectorSignalsInTimingChecks, PerBitViolationsMatchTransitionedBits) {
  // Eight per-bit checks are created for an 8-bit-data vs scalar-clock $setup.
  EXPECT_EQ(
      TimingCheckExpandedCount(TimingCheckKind::kSetup, /*ref=*/1,
                               /*data=*/8, TimingCheckVectorMode::kPerBit),
      8u);

  // Only six of those eight bits transition, so six violations are reported.
  EXPECT_EQ(VectorTransitionViolationCount(/*before=*/0b00101110,
                                           /*after=*/0b01010011, /*width=*/8),
            6u);
}

TEST(VectorSignalsInTimingChecks, VectorTransitionViolationCountEdges) {
  // No bits changed -> no violations, even for a wide vector.
  EXPECT_EQ(VectorTransitionViolationCount(0xFF, 0xFF, 8), 0u);
  // Every bit changed -> one violation per bit.
  EXPECT_EQ(VectorTransitionViolationCount(0x00, 0xFF, 8), 8u);
  // Changes above the declared width are outside the vector and do not count.
  EXPECT_EQ(VectorTransitionViolationCount(0x00, 0xF0, 4), 0u);
  // A single-bit signal transitioning is a single violation.
  EXPECT_EQ(VectorTransitionViolationCount(0, 1, 1), 1u);
}

// §31.8, D4: "If there is a notifier, all the timing checks trigger that
// notifier." Under per-bit expansion the expanded checks share the one notifier
// declared in the check; each per-bit violation drives it through the §31.6
// toggle. Applying that shared toggle once per transitioned bit shows every
// expanded violation funnels into the single notifier -- six toggles for the
// LRM example (net parity even, back to its starting value), and an odd count
// leaves it flipped, proving the toggles are not lost.
TEST(VectorSignalsInTimingChecks, AllPerBitViolationsToggleSharedNotifier) {
  uint32_t six = VectorTransitionViolationCount(0b00101110, 0b01010011, 8);
  ASSERT_EQ(six, 6u);
  Logic4Word notifier{0, 0};
  for (uint32_t i = 0; i < six; ++i) {
    notifier = ToggleNotifierOnViolation(notifier);
  }
  // Six shared toggles from 0: even parity returns to 0, but the notifier was
  // driven by each of the six per-bit violations.
  EXPECT_TRUE(notifier.IsZero());

  uint32_t three = VectorTransitionViolationCount(0b000, 0b111, 3);
  ASSERT_EQ(three, 3u);
  Logic4Word odd{0, 0};
  for (uint32_t i = 0; i < three; ++i) {
    odd = ToggleNotifierOnViolation(odd);
  }
  // Three shared toggles from 0 leave it at 1 -- each violation reached it.
  EXPECT_TRUE(odd.IsOne());
}

}  // namespace
