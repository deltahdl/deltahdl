#include <gtest/gtest.h>

#include "elaborator/sequence_degeneracy.h"

using namespace delta;

namespace {

TEST(SequenceProperty, SequenceUsedAsPropertyMustNotAdmitEmptyMatch) {
  EXPECT_FALSE(IsSequenceUsageLegal(SequenceUsageContext::kAsProperty,
                                    SequenceMatchClass::kAdmitsOnlyEmpty));
  EXPECT_FALSE(IsSequenceUsageLegal(SequenceUsageContext::kAsProperty,
                                    SequenceMatchClass::kAdmitsNoMatch));
  EXPECT_TRUE(
      IsSequenceUsageLegal(SequenceUsageContext::kAsProperty,
                           SequenceMatchClass::kAdmitsAtLeastOneNonempty));
}

}  // namespace
