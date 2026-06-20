#include <gtest/gtest.h>

#include "simulator/specify.h"

using namespace delta;

namespace {

TEST(NegativeTimingCheckNotifierToggle, DelayedViolationToggles) {
  EXPECT_TRUE(NegativeTimingCheckNotifierShouldToggle(true, false));
}

TEST(NegativeTimingCheckNotifierToggle, UndelayedViolationDoesNotToggle) {
  EXPECT_FALSE(NegativeTimingCheckNotifierShouldToggle(false, true));
}

TEST(NegativeTimingCheckNotifierToggle, BothViolationsToggle) {
  EXPECT_TRUE(NegativeTimingCheckNotifierShouldToggle(true, true));
}

}  // namespace
