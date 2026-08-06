#include <gtest/gtest.h>

#include "elaborator/sequence_match_attach.h"

using namespace delta;

namespace {

TEST(AttachedSubroutineScheduling, RegionIsReactive) {
  // §16.11: attached subroutine calls are scheduled in the Reactive region,
  // exactly like an action block.
  EXPECT_EQ(AttachedSubroutineRegion(),
            AttachedSubroutineSchedulingRegion::kReactive);
}

TEST(AttachedSubroutineScheduling, EvaluationDoesNotAwaitCallReturn) {
  // §16.11: assertion evaluation does not wait on, or receive data back
  // from, any attached subroutine.
  EXPECT_FALSE(AssertionEvalWaitsForAttachedSubroutine());
}

TEST(AttachedSubroutineScheduling, ByValueArgumentUsesSampledValues) {
  // §16.11: an actual argument passed by value reads the sampled value of
  // the underlying variable rather than its current value.
  EXPECT_TRUE(ByValueArgumentUsesSampledValuesOfUnderlying());
}

TEST(AttachedSubroutineScheduling, ByValueArgumentMatchesSequenceEvaluation) {
  // §16.11: the sampled value used for a by-value argument is consistent
  // with the value used to evaluate the sequence match it is attached to.
  EXPECT_TRUE(ByValueArgumentValueIsConsistentWithSequenceMatch());
}

}  // namespace
