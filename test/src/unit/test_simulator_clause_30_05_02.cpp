#include <gtest/gtest.h>

#include "simulator/specify.h"

using namespace delta;

namespace {

// SHALL #1: a transition from a known state to x takes the shortest possible
// delay, so the x-bound slots are the minimum of the two contributing
// known-state delays (0->x, 1->x, z->x => slots 6, 8, 11).
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
  EXPECT_EQ(pd.delays[6], 10u);   // min(t0z=30, t01=10)
  EXPECT_EQ(pd.delays[8], 20u);   // min(t1z=50, t10=20)
  EXPECT_EQ(pd.delays[11], 40u);  // min(tz1=40, tz0=60)
}

// SHALL #2: a transition from x to a known state takes the longest possible
// delay, so the x-source slots are the maximum of the two contributing
// known-state delays (x->1, x->0, x->z => slots 7, 9, 10).
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
  EXPECT_EQ(pd.delays[7], 40u);   // max(tz1=40, t01=10)
  EXPECT_EQ(pd.delays[9], 60u);   // max(tz0=60, t10=20)
  EXPECT_EQ(pd.delays[10], 50u);  // max(t1z=50, t0z=30)
}

// Table 30-3 worked usage example: (C => Q) = (5, 12, 17, 10, 6, 22). With all
// six known-state delays distinct, every derived x slot has a unique value, so
// this pins each min/max formula and its operand choice.
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
  EXPECT_EQ(pd.delays[6], 5u);    // 0->x: min(17, 5)
  EXPECT_EQ(pd.delays[7], 10u);   // x->1: max(10, 5)
  EXPECT_EQ(pd.delays[8], 6u);    // 1->x: min(6, 12)
  EXPECT_EQ(pd.delays[9], 22u);   // x->0: max(22, 12)
  EXPECT_EQ(pd.delays[10], 17u);  // x->z: max(6, 17)
  EXPECT_EQ(pd.delays[11], 10u);  // z->x: min(10, 22)
}

// Opening conditional: the derivation applies only when the x transition delays
// are not explicitly specified. A full set of twelve delays leaves the x slots
// untouched.
TEST(SpecifyXTransitionSim, TwelveDelaysPreserveExplicitXSlots) {
  PathDelay pd;
  pd.delay_count = 12;
  for (int i = 0; i < 12; ++i) {
    pd.delays[i] = 100 + static_cast<uint64_t>(i);
  }
  ExpandTransitionDelays(pd);
  for (int i = 6; i < 12; ++i) {
    EXPECT_EQ(pd.delays[i], static_cast<uint64_t>(100 + i)) << "slot " << i;
  }
}

}  // namespace
