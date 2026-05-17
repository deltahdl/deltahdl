#include "simulator/specify.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

TEST(SpecifyXTransitionSim, OneDelayDerivesAllXSlots) {
  PathDelay pd;
  pd.delay_count = 1;
  pd.delays[0] = 7;
  ExpandTransitionDelays(pd);
  for (int i = 6; i < 12; ++i) {
    EXPECT_EQ(pd.delays[i], 7u) << "slot " << i;
  }
}

TEST(SpecifyXTransitionSim, TwoDelaysDeriveXSlots) {
  PathDelay pd;
  pd.delay_count = 2;
  pd.delays[0] = 3;
  pd.delays[1] = 5;
  ExpandTransitionDelays(pd);
  EXPECT_EQ(pd.delays[6], 3u);
  EXPECT_EQ(pd.delays[7], 3u);
  EXPECT_EQ(pd.delays[8], 5u);
  EXPECT_EQ(pd.delays[9], 5u);
  EXPECT_EQ(pd.delays[10], 5u);
  EXPECT_EQ(pd.delays[11], 3u);
}

TEST(SpecifyXTransitionSim, ThreeDelaysDeriveXSlots) {
  PathDelay pd;
  pd.delay_count = 3;
  pd.delays[0] = 2;
  pd.delays[1] = 4;
  pd.delays[2] = 6;
  ExpandTransitionDelays(pd);

  EXPECT_EQ(pd.delays[6], 2u);
  EXPECT_EQ(pd.delays[7], 2u);
  EXPECT_EQ(pd.delays[8], 4u);
  EXPECT_EQ(pd.delays[9], 4u);
  EXPECT_EQ(pd.delays[10], 6u);
  EXPECT_EQ(pd.delays[11], 2u);
}

TEST(SpecifyXTransitionSim, SixDelaysDeriveXSlotsLrmExample) {
  PathDelay pd;
  pd.delay_count = 6;
  pd.delays[0] = 5;
  pd.delays[1] = 12;
  pd.delays[2] = 17;
  pd.delays[3] = 10;
  pd.delays[4] = 6;
  pd.delays[5] = 22;
  ExpandTransitionDelays(pd);
  EXPECT_EQ(pd.delays[6], 5u);
  EXPECT_EQ(pd.delays[7], 10u);
  EXPECT_EQ(pd.delays[8], 6u);
  EXPECT_EQ(pd.delays[9], 22u);
  EXPECT_EQ(pd.delays[10], 17u);
  EXPECT_EQ(pd.delays[11], 10u);
}

TEST(SpecifyXTransitionSim, TwelveDelaysPreserveExplicitXSlots) {
  PathDelay pd;
  pd.delay_count = 12;
  for (int i = 0; i < 12; ++i) {
    pd.delays[i] = static_cast<uint64_t>(100 + i);
  }
  ExpandTransitionDelays(pd);
  for (int i = 6; i < 12; ++i) {
    EXPECT_EQ(pd.delays[i], static_cast<uint64_t>(100 + i)) << "slot " << i;
  }
}

TEST(SpecifyXTransitionSim, ZeroDelaysProduceZeroXSlots) {
  PathDelay pd;
  pd.delay_count = 6;
  for (int i = 0; i < 6; ++i) pd.delays[i] = 0;
  ExpandTransitionDelays(pd);
  for (int i = 6; i < 12; ++i) {
    EXPECT_EQ(pd.delays[i], 0u) << "slot " << i;
  }
}

TEST(SpecifyXTransitionSim, UniformSourceDelaysProduceUniformXSlots) {
  PathDelay pd;
  pd.delay_count = 6;
  for (int i = 0; i < 6; ++i) pd.delays[i] = 42;
  ExpandTransitionDelays(pd);
  for (int i = 6; i < 12; ++i) {
    EXPECT_EQ(pd.delays[i], 42u) << "slot " << i;
  }
}

TEST(SpecifyXTransitionSim, TransitionsToXUseMinimum) {
  PathDelay pd;
  pd.delay_count = 6;
  pd.delays[0] = 10;
  pd.delays[1] = 20;
  pd.delays[2] = 30;
  pd.delays[3] = 40;
  pd.delays[4] = 50;
  pd.delays[5] = 60;
  ExpandTransitionDelays(pd);
  EXPECT_EQ(pd.delays[6], 10u);
  EXPECT_EQ(pd.delays[8], 20u);
  EXPECT_EQ(pd.delays[11], 40u);
}

TEST(SpecifyXTransitionSim, TransitionsFromXUseMaximum) {
  PathDelay pd;
  pd.delay_count = 6;
  pd.delays[0] = 10;
  pd.delays[1] = 20;
  pd.delays[2] = 30;
  pd.delays[3] = 40;
  pd.delays[4] = 50;
  pd.delays[5] = 60;
  ExpandTransitionDelays(pd);
  EXPECT_EQ(pd.delays[7], 40u);
  EXPECT_EQ(pd.delays[9], 60u);
  EXPECT_EQ(pd.delays[10], 50u);
}

}
