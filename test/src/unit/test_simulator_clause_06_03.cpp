// §6.3: Value set

#include "common/arena.h"
#include "common/types.h"
#include <gtest/gtest.h>

using namespace delta;

namespace {

TEST(Types, Logic4WordBasicValues_IsKnown) {
  struct Case {
    Logic4Word val;
    bool expected;
    const char *label;
  };
  const Case kCases[] = {
      {{0, 0}, true, "zero"},
      {{1, 0}, true, "one"},
      {{0, 1}, false, "x"},
      {{1, 1}, false, "z"},
  };
  for (const auto &c : kCases) {
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

} // namespace
