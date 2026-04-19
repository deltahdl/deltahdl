#include "simulator/specify.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

// §30.5.2 / Table 30-3: when the source delays are uniform (count 1), every
// derived x-transition collapses to the same single value, because every
// min/max input is the same t.
TEST(SpecifyXTransitionSim, OneDelayDerivesAllXSlots) {
  PathDelay pd;
  pd.delay_count = 1;
  pd.delays[0] = 7;
  ExpandTransitionDelays(pd);
  for (int i = 6; i < 12; ++i) {
    EXPECT_EQ(pd.delays[i], 7u) << "slot " << i;
  }
}

// §30.5.2 / Table 30-3: with trise/tfall inputs (count 2), non-x slots hold
// [trise, tfall, trise, trise, tfall, tfall]; the algorithm derives x slots
// by running min/max over that layout.
TEST(SpecifyXTransitionSim, TwoDelaysDeriveXSlots) {
  PathDelay pd;
  pd.delay_count = 2;
  pd.delays[0] = 3;  // trise
  pd.delays[1] = 5;  // tfall
  ExpandTransitionDelays(pd);
  EXPECT_EQ(pd.delays[6], 3u);   // 0->x = min(t0z=3, t01=3) = 3
  EXPECT_EQ(pd.delays[7], 3u);   // x->1 = max(tz1=3, t01=3) = 3
  EXPECT_EQ(pd.delays[8], 5u);   // 1->x = min(t1z=5, t10=5) = 5
  EXPECT_EQ(pd.delays[9], 5u);   // x->0 = max(tz0=5, t10=5) = 5
  EXPECT_EQ(pd.delays[10], 5u);  // x->z = max(t1z=5, t0z=3) = 5
  EXPECT_EQ(pd.delays[11], 3u);  // z->x = min(tz1=3, tz0=5) = 3
}

// §30.5.2 / Table 30-3: with trise/tfall/tz inputs (count 3), the z column
// of the non-x layout is distinct, so x-slot derivation now exercises a
// different min/max pairing than count 2.
TEST(SpecifyXTransitionSim, ThreeDelaysDeriveXSlots) {
  PathDelay pd;
  pd.delay_count = 3;
  pd.delays[0] = 2;  // trise
  pd.delays[1] = 4;  // tfall
  pd.delays[2] = 6;  // tz
  ExpandTransitionDelays(pd);
  // Non-x layout after expansion: [2, 4, 6, 2, 6, 4].
  EXPECT_EQ(pd.delays[6], 2u);   // 0->x = min(t0z=6, t01=2) = 2
  EXPECT_EQ(pd.delays[7], 2u);   // x->1 = max(tz1=2, t01=2) = 2
  EXPECT_EQ(pd.delays[8], 4u);   // 1->x = min(t1z=6, t10=4) = 4
  EXPECT_EQ(pd.delays[9], 4u);   // x->0 = max(tz0=4, t10=4) = 4
  EXPECT_EQ(pd.delays[10], 6u);  // x->z = max(t1z=6, t0z=6) = 6
  EXPECT_EQ(pd.delays[11], 2u);  // z->x = min(tz1=2, tz0=4) = 2
}

// §30.5.2 / Table 30-3 usage example: for (C => Q) = (5, 12, 17, 10, 6, 22)
// the LRM publishes the expected derived x-transition delays. Matching them
// exactly is the strongest check that the algorithm is implemented faithfully.
TEST(SpecifyXTransitionSim, SixDelaysDeriveXSlotsLrmExample) {
  PathDelay pd;
  pd.delay_count = 6;
  pd.delays[0] = 5;   // t01
  pd.delays[1] = 12;  // t10
  pd.delays[2] = 17;  // t0z
  pd.delays[3] = 10;  // tz1
  pd.delays[4] = 6;   // t1z
  pd.delays[5] = 22;  // tz0
  ExpandTransitionDelays(pd);
  EXPECT_EQ(pd.delays[6], 5u);   // 0->x = min(17, 5) = 5
  EXPECT_EQ(pd.delays[7], 10u);  // x->1 = max(10, 5) = 10
  EXPECT_EQ(pd.delays[8], 6u);   // 1->x = min(6, 12) = 6
  EXPECT_EQ(pd.delays[9], 22u);  // x->0 = max(22, 12) = 22
  EXPECT_EQ(pd.delays[10], 17u); // x->z = max(6, 17) = 17
  EXPECT_EQ(pd.delays[11], 10u); // z->x = min(10, 22) = 10
}

// §30.5.2: the derivation algorithm applies only when x transitions are not
// explicitly specified. When all twelve delays are given, the explicit x-slot
// values must survive unchanged.
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

// §30.5.2: an all-zero input reduces every min/max computation to zero, so
// every derived x slot must also be zero.
TEST(SpecifyXTransitionSim, ZeroDelaysProduceZeroXSlots) {
  PathDelay pd;
  pd.delay_count = 6;
  for (int i = 0; i < 6; ++i) pd.delays[i] = 0;
  ExpandTransitionDelays(pd);
  for (int i = 6; i < 12; ++i) {
    EXPECT_EQ(pd.delays[i], 0u) << "slot " << i;
  }
}

// §30.5.2: when every input is the same value, each min/max resolves to that
// value, so every derived x slot equals the uniform source value.
TEST(SpecifyXTransitionSim, UniformSourceDelaysProduceUniformXSlots) {
  PathDelay pd;
  pd.delay_count = 6;
  for (int i = 0; i < 6; ++i) pd.delays[i] = 42;
  ExpandTransitionDelays(pd);
  for (int i = 6; i < 12; ++i) {
    EXPECT_EQ(pd.delays[i], 42u) << "slot " << i;
  }
}

// §30.5.2 pessimistic rule 1: transitions TO x shall use the shortest (min)
// of the contributing source delays. Isolated by checking only the three
// "to x" slots with six all-distinct source values.
TEST(SpecifyXTransitionSim, TransitionsToXUseMinimum) {
  PathDelay pd;
  pd.delay_count = 6;
  pd.delays[0] = 10;  // t01
  pd.delays[1] = 20;  // t10
  pd.delays[2] = 30;  // t0z
  pd.delays[3] = 40;  // tz1
  pd.delays[4] = 50;  // t1z
  pd.delays[5] = 60;  // tz0
  ExpandTransitionDelays(pd);
  EXPECT_EQ(pd.delays[6], 10u);   // 0->x = min(30, 10) = 10
  EXPECT_EQ(pd.delays[8], 20u);   // 1->x = min(50, 20) = 20
  EXPECT_EQ(pd.delays[11], 40u);  // z->x = min(40, 60) = 40
}

// §30.5.2 pessimistic rule 2: transitions FROM x shall use the longest (max)
// of the contributing source delays. Isolated by checking only the three
// "from x" slots with six all-distinct source values.
TEST(SpecifyXTransitionSim, TransitionsFromXUseMaximum) {
  PathDelay pd;
  pd.delay_count = 6;
  pd.delays[0] = 10;  // t01
  pd.delays[1] = 20;  // t10
  pd.delays[2] = 30;  // t0z
  pd.delays[3] = 40;  // tz1
  pd.delays[4] = 50;  // t1z
  pd.delays[5] = 60;  // tz0
  ExpandTransitionDelays(pd);
  EXPECT_EQ(pd.delays[7], 40u);   // x->1 = max(40, 10) = 40
  EXPECT_EQ(pd.delays[9], 60u);   // x->0 = max(60, 20) = 60
  EXPECT_EQ(pd.delays[10], 50u);  // x->z = max(50, 30) = 50
}

}  // namespace
