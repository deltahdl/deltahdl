#include "common/types.h"
#include "parser/ast.h"
#include "simulator/specify.h"

#include <gtest/gtest.h>

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

TEST(VectorSignalsInTimingChecks, LrmEightBitDataAgainstScalarClock) {
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kSetup, 1, 8,
                                     TimingCheckVectorMode::kSingle),
            1u);
  EXPECT_EQ(TimingCheckExpandedCount(TimingCheckKind::kSetup, 1, 8,
                                     TimingCheckVectorMode::kPerBit),
            8u);
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

}
