#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"

using namespace delta;

namespace {

TEST(LogicValuesSim, FourBasicValuesEncodeDistinctly) {
  Logic4Word v0{0, 0};
  Logic4Word v1{1, 0};
  Logic4Word vx{0, 1};
  Logic4Word vz{1, 1};
  EXPECT_TRUE(v0.IsZero());
  EXPECT_TRUE(v1.IsOne());
  EXPECT_TRUE(v0.IsKnown());
  EXPECT_TRUE(v1.IsKnown());
  EXPECT_FALSE(vx.IsKnown());
  EXPECT_FALSE(vz.IsKnown());
}

TEST(LogicValuesSim, ZeroComplementsToOne) {
  Logic4Word v0{0, 0};
  auto r = Logic4Not(v0);
  EXPECT_EQ(r.aval & 1u, 1u);
  EXPECT_EQ(r.bval & 1u, 0u);
}

TEST(LogicValuesSim, OneComplementsToZero) {
  Logic4Word v1{1, 0};
  auto r = Logic4Not(v1);
  EXPECT_EQ(r.aval & 1u, 0u);
  EXPECT_EQ(r.bval & 1u, 0u);
}

TEST(LogicValuesSim, ZBehavesLikeXUnderBitwiseNot) {
  Logic4Word vz{1, 1};
  Logic4Word vx{0, 1};
  auto rz = Logic4Not(vz);
  auto rx = Logic4Not(vx);
  EXPECT_EQ(rz.aval, rx.aval);
  EXPECT_EQ(rz.bval, rx.bval);
}

TEST(LogicValuesSim, ZBehavesLikeXUnderBitwiseAndWithOne) {
  Logic4Word v1{1, 0};
  Logic4Word vz{1, 1};
  Logic4Word vx{0, 1};
  auto rz = Logic4And(vz, v1);
  auto rx = Logic4And(vx, v1);
  EXPECT_EQ(rz.aval & 1u, rx.aval & 1u);
  EXPECT_EQ(rz.bval & 1u, rx.bval & 1u);
  EXPECT_EQ(rz.bval & 1u, 1u);
}

TEST(LogicValuesSim, ZAndZeroCollapsesToZero) {
  Logic4Word v0{0, 0};
  Logic4Word vz{1, 1};
  auto r = Logic4And(vz, v0);
  EXPECT_EQ(r.aval & 1u, 0u);
  EXPECT_EQ(r.bval & 1u, 0u);
}

TEST(LogicValuesSim, ZBehavesLikeXUnderBitwiseOrWithZero) {
  Logic4Word v0{0, 0};
  Logic4Word vz{1, 1};
  Logic4Word vx{0, 1};
  auto rz = Logic4Or(vz, v0);
  auto rx = Logic4Or(vx, v0);
  EXPECT_EQ(rz.aval & 1u, rx.aval & 1u);
  EXPECT_EQ(rz.bval & 1u, rx.bval & 1u);
  EXPECT_EQ(rz.bval & 1u, 1u);
}

TEST(LogicValuesSim, ZOrOneCollapsesToOne) {
  Logic4Word v1{1, 0};
  Logic4Word vz{1, 1};
  auto r = Logic4Or(vz, v1);
  EXPECT_EQ(r.aval & 1u, 1u);
  EXPECT_EQ(r.bval & 1u, 0u);
}

TEST(LogicValuesSim, ZBehavesLikeXUnderBitwiseXor) {
  Logic4Word v1{1, 0};
  Logic4Word vz{1, 1};
  Logic4Word vx{0, 1};
  auto rz = Logic4Xor(vz, v1);
  auto rx = Logic4Xor(vx, v1);
  EXPECT_EQ(rz.aval & 1u, rx.aval & 1u);
  EXPECT_EQ(rz.bval & 1u, rx.bval & 1u);
  EXPECT_EQ(rz.bval & 1u, 1u);
}

TEST(LogicValuesSim, FourStateVectorBitsAreIndependentlySettable) {
  Arena arena;
  auto vec = MakeLogic4Vec(arena, 4);

  vec.words[0].aval |= (uint64_t{1} << 1);

  vec.words[0].bval |= (uint64_t{1} << 2);

  vec.words[0].aval |= (uint64_t{1} << 3);
  vec.words[0].bval |= (uint64_t{1} << 3);
  EXPECT_EQ(vec.ToString(), "zx10");
}

}
