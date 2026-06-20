#include <gtest/gtest.h>

#include "simulator/specify.h"

using namespace delta;

namespace {

PathDelay MakePathWithDelays(uint64_t value) {
  PathDelay pd;
  pd.delay_count = 1;
  for (int i = 0; i < 12; ++i) pd.delays[i] = value;
  InitDefaultPulseLimits(pd);
  return pd;
}

TEST(ApplyPulseControlOverride, RejectOnlyMirrorsErrorAcrossAllSlots) {
  PathDelay pd = MakePathWithDelays(10);
  ApplyPulseControlOverride(pd, 3, false, 0);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 3u);
    EXPECT_EQ(pd.error_limit[i], 3u);
  }
}

TEST(ApplyPulseControlOverride, PreservesPropagationDelays) {
  PathDelay pd = MakePathWithDelays(10);
  ApplyPulseControlOverride(pd, 4, true, 8);
  for (int i = 0; i < 12; ++i) EXPECT_EQ(pd.delays[i], 10u);
}

// §30.7.1: when no module path is specified, the reject and error limits apply
// to every module path in the module. A module-wide override applied to each
// path delay sets the same limits on all of them.
TEST(ApplyPulseControlOverride, ModuleWideOverrideAppliesToEveryPath) {
  PathDelay first = MakePathWithDelays(20);
  PathDelay second = MakePathWithDelays(30);
  ApplyPulseControlOverride(first, 4, true, 6);
  ApplyPulseControlOverride(second, 4, true, 6);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(first.reject_limit[i], 4u);
    EXPECT_EQ(first.error_limit[i], 6u);
    EXPECT_EQ(second.reject_limit[i], 4u);
    EXPECT_EQ(second.error_limit[i], 6u);
  }
}

// §30.7.1: when both a path-specific and a non-path-specific PATHPULSE$
// specparam apply to a path, the path-specific values take precedence. The
// module-wide override is applied first and the path-specific override is then
// applied on top, so the path-specific limits win.
TEST(ApplyPulseControlOverride, PathSpecificOverrideTakesPrecedence) {
  PathDelay pd = MakePathWithDelays(40);
  ApplyPulseControlOverride(pd, 2, true, 9);  // module-wide
  ApplyPulseControlOverride(pd, 1, true, 3);  // path-specific
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 1u);
    EXPECT_EQ(pd.error_limit[i], 3u);
  }
}

}  // namespace
