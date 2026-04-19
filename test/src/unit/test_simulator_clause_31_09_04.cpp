#include "simulator/specify.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

// §31.9.4: with the negative-timing-checks invocation option enabled
// and the "disable all timing checks" option off, the feature is
// active and the delayed reference and data signals stay distinct
// from the originals. This is the only combination the LRM treats
// as full negative-value handling.
TEST(NegativeTimingCheckOption, ActiveWhenOptionOnAndChecksNotDisabled) {
  EXPECT_TRUE(NegativeTimingCheckOptionActive(
      /*negative_timing_check_option_enabled=*/true,
      /*all_timing_checks_disabled=*/false));
}

// §31.9.4: a model that references delayed signals can still run
// without the negative-timing-checks option, but in that mode the
// simulator must treat the delayed signals as copies of the
// originals. The predicate flags the mode by returning false.
TEST(NegativeTimingCheckOption, InactiveWhenOptionOff) {
  EXPECT_FALSE(NegativeTimingCheckOptionActive(
      /*negative_timing_check_option_enabled=*/false,
      /*all_timing_checks_disabled=*/false));
}

// §31.9.4: an invocation option that turns off all timing checks
// produces the same collapse as leaving the negative-timing-checks
// option unset — the delayed signals become copies of the
// originals even though the negative option appears to be on.
TEST(NegativeTimingCheckOption, InactiveWhenAllChecksDisabledOverridesOption) {
  EXPECT_FALSE(NegativeTimingCheckOptionActive(
      /*negative_timing_check_option_enabled=*/true,
      /*all_timing_checks_disabled=*/true));
}

// §31.9.4: with neither option set in the active combination, the
// feature is inactive for both reasons the LRM names. The helper
// reports false rather than privileging either disabling mechanism
// over the other.
TEST(NegativeTimingCheckOption, InactiveWhenBothDisabled) {
  EXPECT_FALSE(NegativeTimingCheckOptionActive(
      /*negative_timing_check_option_enabled=*/false,
      /*all_timing_checks_disabled=*/true));
}

}  // namespace
