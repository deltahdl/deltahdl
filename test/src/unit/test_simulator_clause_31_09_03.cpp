#include "simulator/specify.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

TEST(NegativeTimingCheckNotifierToggle, DelayedViolationToggles) {
  EXPECT_TRUE(NegativeTimingCheckNotifierShouldToggle(
      true,
      false));
}

TEST(NegativeTimingCheckNotifierToggle, UndelayedViolationDoesNotToggle) {
  EXPECT_FALSE(NegativeTimingCheckNotifierShouldToggle(
      false,
      true));
}

TEST(NegativeTimingCheckNotifierToggle, BothViolationsToggle) {
  EXPECT_TRUE(NegativeTimingCheckNotifierShouldToggle(
      true,
      true));
}

}
