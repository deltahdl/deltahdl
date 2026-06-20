#include <gtest/gtest.h>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

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

TEST(AssertionStatementKinds, NoImmediateRestrict) {
  EXPECT_FALSE(IsImmediateAssertionKindAllowed(AssertionKind::kRestrict));
  EXPECT_TRUE(IsImmediateAssertionKindAllowed(AssertionKind::kAssert));
  EXPECT_TRUE(IsImmediateAssertionKindAllowed(AssertionKind::kAssume));
  EXPECT_TRUE(IsImmediateAssertionKindAllowed(AssertionKind::kCover));
}

TEST(AssertionStatementKinds, DeferredAssertionCarriesKind) {
  DeferredAssertion da;
  EXPECT_EQ(da.kind, AssertionKind::kAssert);
  da.kind = AssertionKind::kCover;
  EXPECT_EQ(da.kind, AssertionKind::kCover);
  da.kind = AssertionKind::kAssume;
  EXPECT_EQ(da.kind, AssertionKind::kAssume);
}

TEST(AssertionStatementKinds, TwoTimingsConcurrentAndImmediate) {
  EXPECT_NE(AssertionTiming::kImmediate, AssertionTiming::kConcurrent);
  EXPECT_EQ(static_cast<uint8_t>(AssertionTiming::kImmediate), 0u);
  EXPECT_EQ(static_cast<uint8_t>(AssertionTiming::kConcurrent), 1u);
}

TEST(AssertionStatementKinds, ConcurrentTimingImpliesSampledValueSemantics) {
  EXPECT_TRUE(ConcurrentTimingUsesSampledValues(AssertionTiming::kConcurrent));
  EXPECT_FALSE(ConcurrentTimingUsesSampledValues(AssertionTiming::kImmediate));
}

}  // namespace
