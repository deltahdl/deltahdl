#include <gtest/gtest.h>

#include "elaborator/sequence_degeneracy.h"

using namespace delta;

namespace {

// §16.12.2: the sequence_expr of a sequential property shall not admit an empty
// match. This is the property-usage context of the sequence degeneracy check:
// a sequence used directly as a property must be nondegenerate and must not
// admit any empty match. The empty-admitting classes are rejected; only a
// sequence that admits at least one nonempty (and no empty) match is legal as a
// sequential property.
TEST(SequenceProperty, SequenceUsedAsPropertyMustNotAdmitEmptyMatch) {
  // A sequence that admits only an empty match (e.g. a[*0]) is illegal as a
  // sequential property.
  EXPECT_FALSE(IsSequenceUsageLegal(SequenceUsageContext::kAsProperty,
                                    SequenceMatchClass::kAdmitsOnlyEmpty));
  // A sequence that admits no match at all is likewise illegal as a property.
  EXPECT_FALSE(IsSequenceUsageLegal(SequenceUsageContext::kAsProperty,
                                    SequenceMatchClass::kAdmitsNoMatch));
  // A sequence that admits at least one nonempty match is the legal shape for a
  // sequential property.
  EXPECT_TRUE(
      IsSequenceUsageLegal(SequenceUsageContext::kAsProperty,
                           SequenceMatchClass::kAdmitsAtLeastOneNonempty));
}

}  // namespace
