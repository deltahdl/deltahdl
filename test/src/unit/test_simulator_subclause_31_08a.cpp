#include <gtest/gtest.h>

#include <cstdint>

#include "common/types.h"
#include "parser/ast_specify.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

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

TEST(VectorSignalsInTimingChecks, VectorTransitionReportsSingleSetupViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetup;
  tc.ref_signal = "CLK";
  tc.data_signal = "DAT";
  tc.limit = 10;
  mgr.AddTimingCheck(tc);

  EXPECT_TRUE(mgr.CheckSetupViolation("CLK", 105, "DAT", 100));

  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kSetup, 1, 8,
                                     TimingCheckVectorMode::kSingle),
            1u);
}

TEST(VectorSignalsInTimingChecks, PerBitViolationsMatchTransitionedBits) {
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kSetup, 1, 8,
                                     TimingCheckVectorMode::kPerBit),
            8u);

  EXPECT_EQ(VectorTransitionViolationCount(0b00101110, 0b01010011, 8), 6u);
}

TEST(VectorSignalsInTimingChecks, VectorTransitionViolationCountEdges) {
  EXPECT_EQ(VectorTransitionViolationCount(0xFF, 0xFF, 8), 0u);
  EXPECT_EQ(VectorTransitionViolationCount(0x00, 0xFF, 8), 8u);
  EXPECT_EQ(VectorTransitionViolationCount(0x00, 0xF0, 4), 0u);
  EXPECT_EQ(VectorTransitionViolationCount(0, 1, 1), 1u);
}

TEST(VectorSignalsInTimingChecks, AllPerBitViolationsToggleSharedNotifier) {
  uint32_t six = VectorTransitionViolationCount(0b00101110, 0b01010011, 8);
  ASSERT_EQ(six, 6u);
  Logic4Word notifier{0, 0};
  for (uint32_t i = 0; i < six; ++i) {
    notifier = ToggleNotifierOnViolation(notifier);
  }
  EXPECT_TRUE(notifier.IsZero());

  uint32_t three = VectorTransitionViolationCount(0b000, 0b111, 3);
  ASSERT_EQ(three, 3u);
  Logic4Word odd{0, 0};
  for (uint32_t i = 0; i < three; ++i) {
    odd = ToggleNotifierOnViolation(odd);
  }
  EXPECT_TRUE(odd.IsOne());
}

}  // namespace
