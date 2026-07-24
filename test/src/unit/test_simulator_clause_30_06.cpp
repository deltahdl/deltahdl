#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/specify.h"

using namespace delta;

namespace {

// §30.6: when a module mixes a module path delay and distributed delays along
// that path, the larger of the two shall be used. The rule is a two-operand
// maximum, so its only distinguishable behaviors are "module path delay wins"
// and "distributed sum wins" — the two worked examples in the clause exercise
// exactly those outcomes.

// LRM Example 1 (Figure 30-3): module path delay 22 exceeds the distributed
// sum 0 + 1 = 1, so the module path delay is used.
TEST(MixedPathDistributedDelay, ModulePathLargerWinsLrmExample1) {
  EXPECT_EQ(SelectEffectivePathDelay(22, 1), 22u);
}

// LRM Example 2 (Figure 30-4): the distributed sum 10 + 20 = 30 exceeds the
// module path delay 22, so the distributed sum is used.
TEST(MixedPathDistributedDelay, DistributedSumLargerWinsLrmExample2) {
  EXPECT_EQ(SelectEffectivePathDelay(22, 30), 30u);
}

// Boundary between the two winning outcomes: when the module path delay and the
// distributed sum are equal, "the larger of the two" resolves to that shared
// value rather than doubling or otherwise combining them.
TEST(MixedPathDistributedDelay, EqualDelaysYieldThatValue) {
  EXPECT_EQ(SelectEffectivePathDelay(22, 22), 22u);
}

// Negative of the mixing precondition (path delay present, no distributed
// delays along the path): the distributed sum is zero, so the module path delay
// is used unchanged. The clause's rule only mixes when both kinds are present.
TEST(MixedPathDistributedDelay, NoDistributedDelayUsesModulePath) {
  EXPECT_EQ(SelectEffectivePathDelay(22, 0), 22u);
}

// Negative of the mixing precondition in the other direction (distributed
// delays present, no module path delay): the module path delay is zero, so the
// distributed sum is used unchanged.
TEST(MixedPathDistributedDelay, NoModulePathUsesDistributedDelay) {
  EXPECT_EQ(SelectEffectivePathDelay(0, 30), 30u);
}

}  // namespace
