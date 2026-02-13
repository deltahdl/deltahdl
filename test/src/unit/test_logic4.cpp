#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"

using namespace delta;

TEST(Types, Logic4WordBasicValues) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x_val = {0, 1};
  Logic4Word z_val = {1, 1};

  EXPECT_TRUE(zero.IsKnown());
  EXPECT_TRUE(one.IsKnown());
  EXPECT_FALSE(x_val.IsKnown());
  EXPECT_FALSE(z_val.IsKnown());

  EXPECT_TRUE(zero.IsZero());
  EXPECT_TRUE(one.IsOne());
  EXPECT_FALSE(zero.IsOne());
  EXPECT_FALSE(one.IsZero());
}

TEST(Types, Logic4WordAnd) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x_val = {0, 1};

  // 1 & 1 = 1
  auto r1 = Logic4And(one, one);
  EXPECT_EQ(r1.aval, 1);
  EXPECT_EQ(r1.bval, 0);

  // 1 & 0 = 0
  auto r2 = Logic4And(one, zero);
  EXPECT_EQ(r2.aval, 0);
  EXPECT_EQ(r2.bval, 0);

  // 0 & x = 0
  auto r3 = Logic4And(zero, x_val);
  EXPECT_EQ(r3.aval, 0);
  EXPECT_EQ(r3.bval, 0);

  // 1 & x = x
  auto r4 = Logic4And(one, x_val);
  EXPECT_NE(r4.bval, 0);
}

TEST(Types, Logic4WordOr) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x_val = {0, 1};

  // 0 | 0 = 0
  auto r1 = Logic4Or(zero, zero);
  EXPECT_EQ(r1.aval, 0);
  EXPECT_EQ(r1.bval, 0);

  // 1 | 0 = 1
  auto r2 = Logic4Or(one, zero);
  EXPECT_EQ(r2.aval, 1);
  EXPECT_EQ(r2.bval, 0);

  // 1 | x = 1
  auto r3 = Logic4Or(one, x_val);
  EXPECT_EQ(r3.aval, 1);
  EXPECT_EQ(r3.bval, 0);
}

TEST(Types, Logic4WordXor) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};

  // 1 ^ 0 = 1
  auto r1 = Logic4Xor(one, zero);
  EXPECT_EQ(r1.aval, 1);
  EXPECT_EQ(r1.bval, 0);

  // 1 ^ 1 = 0
  auto r2 = Logic4Xor(one, one);
  EXPECT_EQ(r2.aval, 0);
  EXPECT_EQ(r2.bval, 0);
}

TEST(Types, Logic4WordNot) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x_val = {0, 1};

  auto r1 = Logic4Not(zero);
  EXPECT_EQ(r1.aval, ~uint64_t(0));  // all 64 bits flip: 0->1
  EXPECT_EQ(r1.bval, 0);

  auto r2 = Logic4Not(one);
  EXPECT_EQ(r2.aval, ~uint64_t(1));  // bit 0: 1->0, bits 1-63: 0->1
  EXPECT_EQ(r2.bval, 0);

  auto r3 = Logic4Not(x_val);
  EXPECT_NE(r3.bval, 0);
}

TEST(Types, Logic4VecCreationAndToString) {
  Arena arena;
  auto vec = MakeLogic4VecVal(arena, 8, 0xA5);
  EXPECT_EQ(vec.width, 8);
  EXPECT_TRUE(vec.IsKnown());
  EXPECT_EQ(vec.ToUint64(), 0xA5);
  EXPECT_EQ(vec.ToString(), "10100101");
}

TEST(Arena, Allocation) {
  Arena arena;
  const auto* p1 = arena.AllocArray<uint64_t>(10);
  ASSERT_NE(p1, nullptr);
  auto* p2 = arena.AllocArray<uint32_t>(100);
  ASSERT_NE(p2, nullptr);
  EXPECT_NE(p1, reinterpret_cast<const uint64_t*>(p2));
  EXPECT_GT(arena.TotalAllocated(), 0);
}

TEST(Arena, StringAllocation) {
  Arena arena;
  const char* src = "hello";
  auto* s = arena.AllocString(src, 5);
  EXPECT_EQ(std::string_view(s), "hello");
}

TEST(Arena, Reset) {
  Arena arena;
  arena.AllocArray<char>(1000);
  EXPECT_EQ(arena.TotalAllocated(), 1000);
  arena.Reset();
  EXPECT_EQ(arena.TotalAllocated(), 0);
}
