#include "simulator/specify.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

TEST(NegativeTimingCheckOption, ActiveWhenOptionOnAndChecksNotDisabled) {
  EXPECT_TRUE(NegativeTimingCheckOptionActive(
      true,
      false));
}

TEST(NegativeTimingCheckOption, InactiveWhenOptionOff) {
  EXPECT_FALSE(NegativeTimingCheckOptionActive(
      false,
      false));
}

TEST(NegativeTimingCheckOption, InactiveWhenAllChecksDisabledOverridesOption) {
  EXPECT_FALSE(NegativeTimingCheckOptionActive(
      true,
      true));
}

TEST(NegativeTimingCheckOption, InactiveWhenBothDisabled) {
  EXPECT_FALSE(NegativeTimingCheckOptionActive(
      false,
      true));
}

}
