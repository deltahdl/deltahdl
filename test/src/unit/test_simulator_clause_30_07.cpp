#include "simulator/specify.h"

#include <gtest/gtest.h>

#include <cstdint>

using namespace delta;

namespace {

TEST(PulseFiltering, PulseAtErrorLimitPropagates) {
  EXPECT_EQ(ClassifyPulse( 7, 3, 7),
            PulseClassification::kPropagate);
}

TEST(PulseFiltering, PulseAtRejectLimitForcesXWhenErrorHigher) {
  EXPECT_EQ(ClassifyPulse( 3, 3, 7),
            PulseClassification::kForceX);
}

TEST(PulseFiltering, PulseJustBelowErrorLimitForcesX) {
  EXPECT_EQ(ClassifyPulse( 6, 3, 7),
            PulseClassification::kForceX);
}

TEST(PulseFiltering, PulseBelowRejectLimitIsRejected) {
  EXPECT_EQ(ClassifyPulse( 2, 3, 7),
            PulseClassification::kReject);
}

TEST(PulseFiltering, DefaultPulseLimitsMatchEveryTransitionDelay) {
  PathDelay pd;
  pd.delay_count = 12;
  for (int i = 0; i < 12; ++i) pd.delays[i] = static_cast<uint64_t>(10 + i);
  InitDefaultPulseLimits(pd);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], static_cast<uint64_t>(10 + i)) << "slot " << i;
    EXPECT_EQ(pd.error_limit[i], static_cast<uint64_t>(10 + i)) << "slot " << i;
  }
}

TEST(PulseFiltering, DefaultsRejectPulseNarrowerThanPathDelay) {
  PathDelay pd;
  pd.delay_count = 1;
  pd.delays[0] = 10;
  InitDefaultPulseLimits(pd);
  EXPECT_EQ(ClassifyPulse( 5, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kReject);
}

TEST(PulseFiltering, DefaultsPropagatePulseAtPathDelayWidth) {
  PathDelay pd;
  pd.delay_count = 1;
  pd.delays[0] = 10;
  InitDefaultPulseLimits(pd);
  EXPECT_EQ(ClassifyPulse( 10, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kPropagate);
}

TEST(PulseFiltering, TrailingEdgeLimitsGovernFiltering) {
  PathDelay pd;
  pd.delay_count = 2;
  pd.delays[0] = 7;
  pd.delays[1] = 9;
  InitDefaultPulseLimits(pd);

  EXPECT_EQ(ClassifyPulse(8, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kPropagate);

  EXPECT_EQ(ClassifyPulse(8, pd.reject_limit[1], pd.error_limit[1]),
            PulseClassification::kReject);
}

TEST(PulseFiltering, ClassifierProducesOneOfThreeCategories) {
  PulseClassification a = ClassifyPulse(1, 3, 7);
  PulseClassification b = ClassifyPulse(5, 3, 7);
  PulseClassification c = ClassifyPulse(9, 3, 7);
  EXPECT_EQ(a, PulseClassification::kReject);
  EXPECT_EQ(b, PulseClassification::kForceX);
  EXPECT_EQ(c, PulseClassification::kPropagate);
}

}
