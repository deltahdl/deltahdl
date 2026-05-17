#include "common/types.h"
#include "simulator/specify.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

TEST(NotifierUpdate, ZeroTogglesToOne) {
  Logic4Word before{ 0, 0};
  auto after = ToggleNotifierOnViolation(before);
  EXPECT_TRUE(after.IsOne());
}

TEST(NotifierUpdate, OneTogglesToZero) {
  Logic4Word before{ 1, 0};
  auto after = ToggleNotifierOnViolation(before);
  EXPECT_TRUE(after.IsZero());
}

TEST(NotifierUpdate, XResolvesToKnownScalar) {
  Logic4Word before{ 0, 1};
  auto after = ToggleNotifierOnViolation(before);
  EXPECT_TRUE(after.IsKnown());
  EXPECT_TRUE(after.IsZero() || after.IsOne());
}

TEST(NotifierUpdate, ZRemainsZ) {
  Logic4Word before{ 1, 1};
  auto after = ToggleNotifierOnViolation(before);
  EXPECT_EQ(after.aval, 1u);
  EXPECT_EQ(after.bval, 1u);
}

}
