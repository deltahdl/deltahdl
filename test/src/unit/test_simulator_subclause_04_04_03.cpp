#include <gtest/gtest.h>

#include <cstddef>

#include "common/types.h"

using namespace delta;

// §4.4.3 names the PLI regions of a time slot, one subclause each: Preponed,
// Pre-Active, Pre-NBA, Post-NBA, Pre-Observed, Post-Observed, Pre-Re-NBA,
// Post-Re-NBA, Pre-Postponed and Postponed (§4.4.3.1 through §4.4.3.10).
// Preponed and Postponed are simulation regions as well (§4.4.2), so the two
// categories overlap there and a membership read off one cannot be inferred
// from the other.

namespace {

// Independent restatement of the ten §4.4.3 PLI regions.
bool ExpectedPli(Region r) {
  switch (r) {
    case Region::kPreponed:
    case Region::kPreActive:
    case Region::kPreNBA:
    case Region::kPostNBA:
    case Region::kPreObserved:
    case Region::kPostObserved:
    case Region::kPreReNBA:
    case Region::kPostReNBA:
    case Region::kPrePostponed:
    case Region::kPostponed:
      return true;
    default:
      return false;
  }
}

// The PLI region predicate holds for exactly the §4.4.3 members, across every
// region of the time slot rather than only the PLI ones, so a region wrongly
// counted in fails as surely as one wrongly left out.
TEST(PliRegionsSim, PliRegionMembership) {
  for (std::size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    EXPECT_EQ(IsPliRegion(r), ExpectedPli(r))
        << "region ordinal " << static_cast<int>(r);
  }
}

}  // namespace
