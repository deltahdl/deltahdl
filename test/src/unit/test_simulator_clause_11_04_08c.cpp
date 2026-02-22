// §11.4.8: Bitwise operators

#include "common/arena.h"
#include "common/types.h"
#include <gtest/gtest.h>

using namespace delta;

namespace {

TEST(Types, Logic4WordAnd) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x_val = {0, 1};

  struct Case {
    Logic4Word a;
    Logic4Word b;
    uint64_t exp_aval;
    uint64_t exp_bval;
    const char *label;
  };
  const Case kCases[] = {
      {one, one, 1, 0, "1 & 1 = 1"},
      {one, zero, 0, 0, "1 & 0 = 0"},
      {zero, x_val, 0, 0, "0 & x = 0"},
  };
  for (const auto &c : kCases) {
    auto r = Logic4And(c.a, c.b);
    EXPECT_EQ(r.aval, c.exp_aval) << c.label;
    EXPECT_EQ(r.bval, c.exp_bval) << c.label;
  }

  // 1 & x = x
  auto r4 = Logic4And(one, x_val);
  EXPECT_NE(r4.bval, 0);
}

TEST(Types, Logic4WordOr) {
  Logic4Word zero = {0, 0};
  Logic4Word one = {1, 0};
  Logic4Word x_val = {0, 1};

  struct Case {
    Logic4Word a;
    Logic4Word b;
    uint64_t exp_aval;
    uint64_t exp_bval;
    const char *label;
  };
  const Case kCases[] = {
      {zero, zero, 0, 0, "0 | 0 = 0"},
      {one, zero, 1, 0, "1 | 0 = 1"},
      {one, x_val, 1, 0, "1 | x = 1"},
  };
  for (const auto &c : kCases) {
    auto r = Logic4Or(c.a, c.b);
    EXPECT_EQ(r.aval, c.exp_aval) << c.label;
    EXPECT_EQ(r.bval, c.exp_bval) << c.label;
  }
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
  EXPECT_EQ(r1.aval, ~uint64_t(0)); // all 64 bits flip: 0->1
  EXPECT_EQ(r1.bval, 0);

  auto r2 = Logic4Not(one);
  EXPECT_EQ(r2.aval, ~uint64_t(1)); // bit 0: 1->0, bits 1-63: 0->1
  EXPECT_EQ(r2.bval, 0);

  auto r3 = Logic4Not(x_val);
  EXPECT_NE(r3.bval, 0);
}

} // namespace
