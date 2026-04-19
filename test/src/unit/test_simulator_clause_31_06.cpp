#include "common/types.h"
#include "simulator/specify.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

// §31.6 Table 31-13: a notifier holding 0 flips to 1 after a violation.
TEST(NotifierUpdate, ZeroTogglesToOne) {
  Logic4Word before{/*aval=*/0, /*bval=*/0};
  auto after = ToggleNotifierOnViolation(before);
  EXPECT_TRUE(after.IsOne());
}

// §31.6 Table 31-13: a notifier holding 1 flips to 0 after a violation.
TEST(NotifierUpdate, OneTogglesToZero) {
  Logic4Word before{/*aval=*/1, /*bval=*/0};
  auto after = ToggleNotifierOnViolation(before);
  EXPECT_TRUE(after.IsZero());
}

// §31.6 Table 31-13: the LRM allows either 0 or 1 when the pre-state is
// x. The result must be a known scalar — never x or z.
TEST(NotifierUpdate, XResolvesToKnownScalar) {
  Logic4Word before{/*aval=*/0, /*bval=*/1};
  auto after = ToggleNotifierOnViolation(before);
  EXPECT_TRUE(after.IsKnown());
  EXPECT_TRUE(after.IsZero() || after.IsOne());
}

// §31.6 Table 31-13: a notifier holding z is left unchanged so an
// unconnected or tri-stated notifier cannot be driven by violations.
TEST(NotifierUpdate, ZRemainsZ) {
  Logic4Word before{/*aval=*/1, /*bval=*/1};
  auto after = ToggleNotifierOnViolation(before);
  EXPECT_EQ(after.aval, 1u);
  EXPECT_EQ(after.bval, 1u);
}

}  // namespace
