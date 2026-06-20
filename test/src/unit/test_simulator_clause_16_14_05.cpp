#include <gtest/gtest.h>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.14.5: a concurrent assertion statement used outside procedural code uses
// `always` semantics — a new evaluation attempt begins at every occurrence of
// the leading clock event, so the attempt count tracks the leading clock ticks
// and the property is checked from the beginning to the end of simulation.
TEST(StaticConcurrentAssertion, StartsAttemptOnEachLeadingClock) {
  EXPECT_EQ(StaticConcurrentAssertionAttemptsStarted(0), 0);
  EXPECT_EQ(StaticConcurrentAssertionAttemptsStarted(1), 1);
  EXPECT_EQ(StaticConcurrentAssertionAttemptsStarted(5), 5);
}

// §16.14.5: an `assert property (ps) action_block` outside procedural code is
// equivalent to `always assert property (ps) action_block;`.
TEST(StaticConcurrentAssertion, AssertEquivalentToAlwaysAssert) {
  EXPECT_TRUE(StaticAssertEquivalentToAlwaysAssert());
}

// §16.14.5: likewise, a `cover property (ps) statement_or_null` outside
// procedural code is equivalent to `always cover property (ps)
// statement_or_null`.
TEST(StaticConcurrentAssertion, CoverEquivalentToAlwaysCover) {
  EXPECT_TRUE(StaticCoverEquivalentToAlwaysCover());
}

}  // namespace
