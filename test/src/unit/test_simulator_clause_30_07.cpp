#include "simulator/specify.h"

#include <gtest/gtest.h>

#include <cstdint>

using namespace delta;

namespace {

// §30.7 R6: a pulse whose width equals the error limit is on the propagate
// side of the boundary ("greater than or equal to the error limit"), so it
// must emerge unfiltered rather than being forced to X.
TEST(PulseFiltering, PulseAtErrorLimitPropagates) {
  EXPECT_EQ(ClassifyPulse(/*width=*/7, /*reject=*/3, /*error=*/7),
            PulseClassification::kPropagate);
}

// §30.7 R6: widths strictly larger than the error limit must also propagate
// — classification does not flip once above the boundary.
TEST(PulseFiltering, PulseAboveErrorLimitPropagates) {
  EXPECT_EQ(ClassifyPulse(/*width=*/12, /*reject=*/3, /*error=*/7),
            PulseClassification::kPropagate);
}

// §30.7 R6: width equal to the reject limit (and strictly below the error
// limit) falls in the forced-X band, not in the reject band.
TEST(PulseFiltering, PulseAtRejectLimitForcesXWhenErrorHigher) {
  EXPECT_EQ(ClassifyPulse(/*width=*/3, /*reject=*/3, /*error=*/7),
            PulseClassification::kForceX);
}

// §30.7 R6: any width strictly between reject and error limits must force
// the output to X.
TEST(PulseFiltering, PulseStrictlyBetweenLimitsForcesX) {
  EXPECT_EQ(ClassifyPulse(/*width=*/5, /*reject=*/3, /*error=*/7),
            PulseClassification::kForceX);
}

// §30.7 R6: a width one below the error limit is still within the X band,
// so the classifier must not mistake it for propagation.
TEST(PulseFiltering, PulseJustBelowErrorLimitForcesX) {
  EXPECT_EQ(ClassifyPulse(/*width=*/6, /*reject=*/3, /*error=*/7),
            PulseClassification::kForceX);
}

// §30.7 R6: widths strictly below the reject limit are rejected outright;
// no pulse emerges on the output.
TEST(PulseFiltering, PulseBelowRejectLimitIsRejected) {
  EXPECT_EQ(ClassifyPulse(/*width=*/2, /*reject=*/3, /*error=*/7),
            PulseClassification::kReject);
}

// §30.7 R6 edge case: a zero-width pulse with any non-zero reject limit
// must fall below the reject limit and be rejected.
TEST(PulseFiltering, ZeroWidthPulseIsRejected) {
  EXPECT_EQ(ClassifyPulse(/*width=*/0, /*reject=*/1, /*error=*/5),
            PulseClassification::kReject);
}

// §30.7 R5 + R6: the invariant error_limit >= reject_limit collapses to
// equality at the boundary. When both limits coincide, the X band is
// empty, so a width at or above the limit propagates.
TEST(PulseFiltering, EqualLimitsNoXBandWidthAtLimitPropagates) {
  EXPECT_EQ(ClassifyPulse(/*width=*/5, /*reject=*/5, /*error=*/5),
            PulseClassification::kPropagate);
}

// §30.7 R5 + R6: when reject equals error, widths strictly below the
// shared limit must be rejected (still no X band at all).
TEST(PulseFiltering, EqualLimitsNoXBandWidthBelowLimitIsRejected) {
  EXPECT_EQ(ClassifyPulse(/*width=*/4, /*reject=*/5, /*error=*/5),
            PulseClassification::kReject);
}

// §30.7 R7: after initialization from a PathDelay, every transition slot
// must have reject_limit and error_limit equal to that slot's delay.
TEST(PulseFiltering, DefaultPulseLimitsMatchEveryTransitionDelay) {
  PathDelay pd;
  pd.delay_count = 12;
  for (int i = 0; i < 12; ++i) pd.delays[i] = static_cast<uint64_t>(10 + i);
  InitDefaultPulseLimits(pd);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], static_cast<uint64_t>(10 + i)) << "slot " << i;
    EXPECT_EQ(pd.error_limit[i], static_cast<uint64_t>(10 + i)) << "slot " << i;
  }
}

// §30.7 R1 + R2 + R7: with default limits, a pulse narrower than the
// module path delay fails both the error and reject comparisons, matching
// the inertial-delay default of rejecting all such pulses.
TEST(PulseFiltering, DefaultsRejectPulseNarrowerThanPathDelay) {
  PathDelay pd;
  pd.delay_count = 1;
  pd.delays[0] = 10;
  InitDefaultPulseLimits(pd);
  EXPECT_EQ(ClassifyPulse(/*width=*/5, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kReject);
}

// §30.7 R6 + R7 boundary: a pulse whose width exactly equals the module
// path delay reaches the default error limit and must propagate.
TEST(PulseFiltering, DefaultsPropagatePulseAtPathDelayWidth) {
  PathDelay pd;
  pd.delay_count = 1;
  pd.delays[0] = 10;
  InitDefaultPulseLimits(pd);
  EXPECT_EQ(ClassifyPulse(/*width=*/10, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kPropagate);
}

// §30.7 R8: when the rise and fall delays differ, the limits sourced from
// the trailing-edge slot govern filtering. The same pulse width can
// propagate against rise limits yet be rejected against fall limits.
TEST(PulseFiltering, TrailingEdgeLimitsGovernFiltering) {
  PathDelay pd;
  pd.delay_count = 2;
  pd.delays[0] = 7;  // trise
  pd.delays[1] = 9;  // tfall
  InitDefaultPulseLimits(pd);
  // Width 8 against the rise slot [0] is >= 7 -> propagate.
  EXPECT_EQ(ClassifyPulse(8, pd.reject_limit[0], pd.error_limit[0]),
            PulseClassification::kPropagate);
  // Same width 8 against the fall slot [1] is < 9 -> reject (default
  // limits still collapse the X band to nothing).
  EXPECT_EQ(ClassifyPulse(8, pd.reject_limit[1], pd.error_limit[1]),
            PulseClassification::kReject);
}

// §30.7 R3: the classifier must return exactly one of the three
// categories. Enumerate the three underlying values to lock down the
// contract that no fourth outcome is ever returned.
TEST(PulseFiltering, ClassifierProducesOneOfThreeCategories) {
  PulseClassification a = ClassifyPulse(1, 3, 7);
  PulseClassification b = ClassifyPulse(5, 3, 7);
  PulseClassification c = ClassifyPulse(9, 3, 7);
  EXPECT_EQ(a, PulseClassification::kReject);
  EXPECT_EQ(b, PulseClassification::kForceX);
  EXPECT_EQ(c, PulseClassification::kPropagate);
}

}  // namespace
