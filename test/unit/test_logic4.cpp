#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"

using namespace delta;

TEST(Types, Logic4WordBasicValues) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x_val = {0, 1};
  Logic4Word z_val = {1, 1};

  EXPECT_TRUE(zero.is_known());
  EXPECT_TRUE(one.is_known());
  EXPECT_FALSE(x_val.is_known());
  EXPECT_FALSE(z_val.is_known());

  EXPECT_TRUE(zero.is_zero());
  EXPECT_TRUE(one.is_one());
  EXPECT_FALSE(zero.is_one());
  EXPECT_FALSE(one.is_zero());
}

TEST(Types, Logic4WordAnd) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x_val = {0, 1};

  // 1 & 1 = 1
  auto r1 = logic4_and(one, one);
  EXPECT_EQ(r1.aval, 1);
  EXPECT_EQ(r1.bval, 0);

  // 1 & 0 = 0
  auto r2 = logic4_and(one, zero);
  EXPECT_EQ(r2.aval, 0);
  EXPECT_EQ(r2.bval, 0);

  // 0 & x = 0
  auto r3 = logic4_and(zero, x_val);
  EXPECT_EQ(r3.aval, 0);
  EXPECT_EQ(r3.bval, 0);

  // 1 & x = x
  auto r4 = logic4_and(one, x_val);
  EXPECT_NE(r4.bval, 0);
}

TEST(Types, Logic4WordOr) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x_val = {0, 1};

  // 0 | 0 = 0
  auto r1 = logic4_or(zero, zero);
  EXPECT_EQ(r1.aval, 0);
  EXPECT_EQ(r1.bval, 0);

  // 1 | 0 = 1
  auto r2 = logic4_or(one, zero);
  EXPECT_EQ(r2.aval, 1);
  EXPECT_EQ(r2.bval, 0);

  // 1 | x = 1
  auto r3 = logic4_or(one, x_val);
  EXPECT_EQ(r3.aval, 1);
  EXPECT_EQ(r3.bval, 0);
}

TEST(Types, Logic4WordXor) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};

  // 1 ^ 0 = 1
  auto r1 = logic4_xor(one, zero);
  EXPECT_EQ(r1.aval, 1);
  EXPECT_EQ(r1.bval, 0);

  // 1 ^ 1 = 0
  auto r2 = logic4_xor(one, one);
  EXPECT_EQ(r2.aval, 0);
  EXPECT_EQ(r2.bval, 0);
}

TEST(Types, Logic4WordNot) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x_val = {0, 1};

  auto r1 = logic4_not(zero);
  EXPECT_EQ(r1.aval, ~uint64_t(0));  // all 64 bits flip: 0->1
  EXPECT_EQ(r1.bval, 0);

  auto r2 = logic4_not(one);
  EXPECT_EQ(r2.aval, ~uint64_t(1));  // bit 0: 1->0, bits 1-63: 0->1
  EXPECT_EQ(r2.bval, 0);

  auto r3 = logic4_not(x_val);
  EXPECT_NE(r3.bval, 0);
}

TEST(Types, Logic4VecCreationAndToString) {
  Arena arena;
  auto vec = make_logic4_vec_val(arena, 8, 0xA5);
  EXPECT_EQ(vec.width, 8);
  EXPECT_TRUE(vec.is_known());
  EXPECT_EQ(vec.to_uint64(), 0xA5);
  EXPECT_EQ(vec.to_string(), "10100101");
}

TEST(Arena, Allocation) {
  Arena arena;
  const auto* p1 = arena.alloc_array<uint64_t>(10);
  ASSERT_NE(p1, nullptr);
  auto* p2 = arena.alloc_array<uint32_t>(100);
  ASSERT_NE(p2, nullptr);
  EXPECT_NE(p1, reinterpret_cast<const uint64_t*>(p2));
  EXPECT_GT(arena.total_allocated(), 0);
}

TEST(Arena, StringAllocation) {
  Arena arena;
  const char* src = "hello";
  auto* s = arena.alloc_string(src, 5);
  EXPECT_EQ(std::string_view(s), "hello");
}

TEST(Arena, Reset) {
  Arena arena;
  arena.alloc_array<char>(1000);
  EXPECT_EQ(arena.total_allocated(), 1000);
  arena.reset();
  EXPECT_EQ(arena.total_allocated(), 0);
}
