#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"

using namespace delta;

namespace {

// §6.3.1 ¶1: "The SystemVerilog value set consists of the following four basic
// values: 0, 1, x, z." Each basic value has a distinct dual-rail encoding the
// runtime can recognize via Logic4Word's IsZero/IsOne/IsKnown predicates.
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

// §6.3.1 ¶2: "The values 0 and 1 are logical complements of one another."
// Production code applies this rule via Logic4Not on a Logic4Word holding 0:
// the result must be a known 1.
TEST(LogicValuesSim, ZeroComplementsToOne) {
  Logic4Word v0{0, 0};
  auto r = Logic4Not(v0);
  EXPECT_EQ(r.aval & 1u, 1u);
  EXPECT_EQ(r.bval & 1u, 0u);
}

// §6.3.1 ¶2: complementing 1 must yield a known 0.
TEST(LogicValuesSim, OneComplementsToZero) {
  Logic4Word v1{1, 0};
  auto r = Logic4Not(v1);
  EXPECT_EQ(r.aval & 1u, 0u);
  EXPECT_EQ(r.bval & 1u, 0u);
}

// §6.3.1 ¶3: "When the z value is ... encountered in an expression, the effect
// is usually the same as an x value." Bitwise NOT on z must produce the same
// dual-rail encoding as bitwise NOT on x — both unknown.
TEST(LogicValuesSim, ZBehavesLikeXUnderBitwiseNot) {
  Logic4Word vz{1, 1};
  Logic4Word vx{0, 1};
  auto rz = Logic4Not(vz);
  auto rx = Logic4Not(vx);
  EXPECT_EQ(rz.aval, rx.aval);
  EXPECT_EQ(rz.bval, rx.bval);
}

// §6.3.1 ¶3: bitwise AND of z with a known 1 must yield the same unknown
// result as AND of x with 1.
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

// §6.3.1 ¶3 edge case: z AND a known 0 must collapse to the controlling 0,
// matching the behavior of x AND 0 — confirming z does not pass through a
// controlling AND input.
TEST(LogicValuesSim, ZAndZeroCollapsesToZero) {
  Logic4Word v0{0, 0};
  Logic4Word vz{1, 1};
  auto r = Logic4And(vz, v0);
  EXPECT_EQ(r.aval & 1u, 0u);
  EXPECT_EQ(r.bval & 1u, 0u);
}

// §6.3.1 ¶3: bitwise OR of z with a known 0 must yield the same unknown
// result as OR of x with 0.
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

// §6.3.1 ¶3 edge case: z OR a known 1 must collapse to the controlling 1.
TEST(LogicValuesSim, ZOrOneCollapsesToOne) {
  Logic4Word v1{1, 0};
  Logic4Word vz{1, 1};
  auto r = Logic4Or(vz, v1);
  EXPECT_EQ(r.aval & 1u, 1u);
  EXPECT_EQ(r.bval & 1u, 0u);
}

// §6.3.1 ¶3: bitwise XOR of z with a known 1 must yield the same unknown
// result as XOR of x with 1 — XOR has no controlling value, so any unknown
// operand makes the result unknown.
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

// §6.3.1 ¶5: "All bits of 4-state vectors can be independently set to one of
// the four basic values." Build a 4-bit vector containing one of each value
// (z, x, 1, 0 from MSB to LSB) and verify each bit is preserved independently
// when serialized via the production ToString routine.
TEST(LogicValuesSim, FourStateVectorBitsAreIndependentlySettable) {
  Arena arena;
  auto vec = MakeLogic4Vec(arena, 4);
  // bit 0 = 0: aval=0, bval=0 (default)
  // bit 1 = 1: aval bit set
  vec.words[0].aval |= (uint64_t{1} << 1);
  // bit 2 = x: bval bit set
  vec.words[0].bval |= (uint64_t{1} << 2);
  // bit 3 = z: aval and bval bits set
  vec.words[0].aval |= (uint64_t{1} << 3);
  vec.words[0].bval |= (uint64_t{1} << 3);
  EXPECT_EQ(vec.ToString(), "zx10");
}

}  // namespace
