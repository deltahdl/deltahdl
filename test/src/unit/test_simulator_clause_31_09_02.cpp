#include "simulator/specify.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

// §31.9.2: with positive setup and hold (Figure 31-4), the violation window
// straddles the reference edge and the condition applies to both signals.
TEST(NegativeTimingConditionRoles, TimestampBothNonNegativeIsBoth) {
  EXPECT_EQ(TimestampConditionRole( 5, 10),
            NegativeTimingConditionRole::kBoth);
}

TEST(NegativeTimingConditionRoles, TimecheckBothNonNegativeIsBoth) {
  EXPECT_EQ(TimecheckConditionRole( 5, 10),
            NegativeTimingConditionRole::kBoth);
}

// Degenerate guard: when neither limit is positive there is no first/second
// distinction to anchor an association to a single signal.
TEST(NegativeTimingConditionRoles, BothNegativeIsNone) {
  EXPECT_EQ(TimestampConditionRole(-1, -1), NegativeTimingConditionRole::kNone);
  EXPECT_EQ(TimecheckConditionRole(-1, -1), NegativeTimingConditionRole::kNone);
}

// §31.9.2: a negative setup makes the timecheck condition associate with the
// data signal (the one transitioning second) and the timestamp with the ref.
// A zero hold beside the negative setup also pins the strict `< 0` boundary
// (zero is non-negative, so the case still resolves as negative-setup).
TEST(NegativeTimingConditionRoles, NegativeSetupZeroHoldMatchesNegativeSetup) {
  EXPECT_EQ(TimestampConditionRole( -5, 0),
            NegativeTimingConditionRole::kRef);
  EXPECT_EQ(TimecheckConditionRole( -5, 0),
            NegativeTimingConditionRole::kData);
}

// §31.9.2: a negative hold makes the timecheck condition associate with the
// reference signal and the timestamp with the data; a zero setup pins the
// strict `< 0` boundary on the other operand.
TEST(NegativeTimingConditionRoles, ZeroSetupNegativeHoldMatchesNegativeHold) {
  EXPECT_EQ(TimestampConditionRole( 0, -5),
            NegativeTimingConditionRole::kData);
  EXPECT_EQ(TimecheckConditionRole( 0, -5),
            NegativeTimingConditionRole::kRef);
}

}
