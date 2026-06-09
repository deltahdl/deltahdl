#include "simulator/specify.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

// §31.9.4 C1: negative-value support in $setuphold/$recrem is gated by an
// invocation option, and when that option is active the requested delay on the
// internally delayed signal is applied.
TEST(NegativeTimingCheckOption, OptionEnablesNegativeHandlingAndAppliesDelay) {
  const bool active = NegativeTimingCheckOptionActive(
      true,
      false);
  EXPECT_TRUE(active);
  EXPECT_EQ(EffectiveTimingCheckSignalDelay(7, active), 7);
}

// §31.9.4 C2: run without the option enabled — the delayed reference and data
// signals become copies of the originals, i.e. no delay is applied.
TEST(NegativeTimingCheckOption, WithoutOptionDelayedSignalsAreCopies) {
  const bool active = NegativeTimingCheckOptionActive(
      false,
      false);
  EXPECT_FALSE(active);
  EXPECT_EQ(EffectiveTimingCheckSignalDelay(7, active), 0);
}

// §31.9.4 C3: an invocation option that switches off all timing checks forces
// the same collapse-to-copies, overriding an otherwise-enabled option.
TEST(NegativeTimingCheckOption, AllChecksOffDelayedSignalsAreCopies) {
  const bool active = NegativeTimingCheckOptionActive(
      true,
      true);
  EXPECT_FALSE(active);
  EXPECT_EQ(EffectiveTimingCheckSignalDelay(7, active), 0);
}

}
