#include <gtest/gtest.h>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.2: "An assertion appears as an assertion statement that states the
// verification function to be performed.  The statement shall be of one of
// the following kinds: assert, assume, cover, restrict."  Observe that the
// simulator carries all four kinds and they are distinct values.
TEST(AssertionStatementKinds, AssertionKindHasFourDistinctValues) {
  AssertionKind kinds[] = {
      AssertionKind::kAssert,
      AssertionKind::kAssume,
      AssertionKind::kCover,
      AssertionKind::kRestrict,
  };
  EXPECT_EQ(static_cast<uint8_t>(kinds[0]), 0u);
  EXPECT_EQ(static_cast<uint8_t>(kinds[1]), 1u);
  EXPECT_EQ(static_cast<uint8_t>(kinds[2]), 2u);
  EXPECT_EQ(static_cast<uint8_t>(kinds[3]), 3u);
}

// §16.2: "There is no immediate restrict assertion statement."  Observe
// that IsImmediateAssertionKindAllowed rejects kRestrict and admits the
// other three kinds.
TEST(AssertionStatementKinds, NoImmediateRestrict) {
  EXPECT_FALSE(IsImmediateAssertionKindAllowed(AssertionKind::kRestrict));
  EXPECT_TRUE(IsImmediateAssertionKindAllowed(AssertionKind::kAssert));
  EXPECT_TRUE(IsImmediateAssertionKindAllowed(AssertionKind::kAssume));
  EXPECT_TRUE(IsImmediateAssertionKindAllowed(AssertionKind::kCover));
}

// §16.2: the deferred-immediate queue entry carries an AssertionKind so
// the §16.2 classification survives the simulator boundary.  Observe that
// DeferredAssertion defaults to kAssert and can be set to each of the
// other §16.2 kinds.
TEST(AssertionStatementKinds, DeferredAssertionCarriesKind) {
  DeferredAssertion da;
  EXPECT_EQ(da.kind, AssertionKind::kAssert);
  da.kind = AssertionKind::kCover;
  EXPECT_EQ(da.kind, AssertionKind::kCover);
  da.kind = AssertionKind::kAssume;
  EXPECT_EQ(da.kind, AssertionKind::kAssume);
}

// §16.2: "There are two kinds of assertions: concurrent and immediate."
// Observe that the AssertionTiming enum carries the two distinct timings
// and that they are not aliased.
TEST(AssertionStatementKinds, TwoTimingsConcurrentAndImmediate) {
  EXPECT_NE(AssertionTiming::kImmediate, AssertionTiming::kConcurrent);
  EXPECT_EQ(static_cast<uint8_t>(AssertionTiming::kImmediate), 0u);
  EXPECT_EQ(static_cast<uint8_t>(AssertionTiming::kConcurrent), 1u);
}

// §16.2: "Concurrent assertions are based on clock semantics and use
// sampled values of their expressions."  Observe that the predicate
// reports sampled-value semantics for concurrent timing and not for
// immediate timing — pairing the §16.2 classification with §16.5.1.
TEST(AssertionStatementKinds, ConcurrentTimingImpliesSampledValueSemantics) {
  EXPECT_TRUE(ConcurrentTimingUsesSampledValues(AssertionTiming::kConcurrent));
  EXPECT_FALSE(ConcurrentTimingUsesSampledValues(AssertionTiming::kImmediate));
}

}  // namespace
