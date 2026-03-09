#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"

using namespace delta;

namespace {

TEST(Types, Logic4WordBasicValues_IsKnown) {
  struct Case {
    Logic4Word val;
    bool expected;
    const char* label;
  };
  const Case kCases[] = {
      {{0, 0}, true, "zero"},
      {{1, 0}, true, "one"},
      {{0, 1}, false, "x"},
      {{1, 1}, false, "z"},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(c.val.IsKnown(), c.expected) << c.label;
  }
}

TEST(Types, Logic4WordBasicValues_IsZeroIsOne) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};

  EXPECT_TRUE(zero.IsZero());
  EXPECT_TRUE(one.IsOne());
  EXPECT_FALSE(zero.IsOne());
  EXPECT_FALSE(one.IsZero());
}

TEST(Types, Logic4VecCreationAndToString) {
  Arena arena;
  auto vec = MakeLogic4VecVal(arena, 8, 0xA5);
  EXPECT_EQ(vec.width, 8);
  EXPECT_TRUE(vec.IsKnown());
  EXPECT_EQ(vec.ToUint64(), 0xA5);
  EXPECT_EQ(vec.ToString(), "10100101");
}

TEST(Types, Logic4Not_ComplementProperty) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  auto not_zero = Logic4Not(zero);
  auto not_one = Logic4Not(one);
  EXPECT_TRUE(not_zero.IsOne());
  EXPECT_TRUE(not_one.IsZero());
}

TEST(Types, Logic4Not_UnknownValues) {
  Logic4Word x = {0, 1};
  Logic4Word z = {1, 1};
  auto not_x = Logic4Not(x);
  auto not_z = Logic4Not(z);
  EXPECT_FALSE(not_x.IsKnown());
  EXPECT_FALSE(not_z.IsKnown());
}

TEST(Types, Logic4And_WithUnknowns) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x = {0, 1};

  auto zero_and_x = Logic4And(zero, x);
  EXPECT_TRUE(zero_and_x.IsZero());

  auto one_and_x = Logic4And(one, x);
  EXPECT_FALSE(one_and_x.IsKnown());

  auto x_and_x = Logic4And(x, x);
  EXPECT_FALSE(x_and_x.IsKnown());
}

TEST(Types, Logic4Or_WithUnknowns) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x = {0, 1};

  auto one_or_x = Logic4Or(one, x);
  EXPECT_TRUE(one_or_x.IsOne());

  auto zero_or_x = Logic4Or(zero, x);
  EXPECT_FALSE(zero_or_x.IsKnown());
}

TEST(Types, Logic4Xor_WithUnknowns) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x = {0, 1};

  auto zero_xor_one = Logic4Xor(zero, one);
  EXPECT_TRUE(zero_xor_one.IsOne());

  auto zero_xor_x = Logic4Xor(zero, x);
  EXPECT_FALSE(zero_xor_x.IsKnown());

  auto one_xor_x = Logic4Xor(one, x);
  EXPECT_FALSE(one_xor_x.IsKnown());
}

TEST(Types, Logic4AndOr_KnownValues) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};

  auto and_00 = Logic4And(zero, zero);
  auto and_01 = Logic4And(zero, one);
  auto and_10 = Logic4And(one, zero);
  auto and_11 = Logic4And(one, one);
  EXPECT_TRUE(and_00.IsZero());
  EXPECT_TRUE(and_01.IsZero());
  EXPECT_TRUE(and_10.IsZero());
  EXPECT_TRUE(and_11.IsOne());

  auto or_00 = Logic4Or(zero, zero);
  auto or_01 = Logic4Or(zero, one);
  auto or_10 = Logic4Or(one, zero);
  auto or_11 = Logic4Or(one, one);
  EXPECT_TRUE(or_00.IsZero());
  EXPECT_TRUE(or_01.IsOne());
  EXPECT_TRUE(or_10.IsOne());
  EXPECT_TRUE(or_11.IsOne());
}

TEST(Types, Logic4And_ZTreatedAsX) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word z = {1, 1};

  auto zero_and_z = Logic4And(zero, z);
  EXPECT_TRUE(zero_and_z.IsZero());

  auto one_and_z = Logic4And(one, z);
  EXPECT_FALSE(one_and_z.IsKnown());
}

TEST(Types, Logic4Vec_XZToString) {
  Arena arena;
  auto vec = MakeLogic4Vec(arena, 4);

  vec.words[0].aval = 0b1010;
  vec.words[0].bval = 0b0110;
  EXPECT_EQ(vec.ToString(), "1xz0");
  EXPECT_FALSE(vec.IsKnown());
}

TEST(Types, Logic2Vec_BasicOperations) {
  Logic2Vec vec;
  vec.width = 8;
  vec.nwords = 1;
  uint64_t storage = 0xFF;
  vec.words = &storage;
  EXPECT_EQ(vec.ToUint64(), 0xFF);
}

}  // namespace
