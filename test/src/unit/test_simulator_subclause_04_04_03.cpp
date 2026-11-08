#include <gtest/gtest.h>

#include <cstddef>

#include "common/types.h"

using namespace delta;

namespace {

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

TEST(PliRegionsSim, PliRegionMembership) {
  for (std::size_t i = 0; i < kRegionCount; ++i) {
    auto r = static_cast<Region>(i);
    EXPECT_EQ(IsPliRegion(r), ExpectedPli(r))
        << "region ordinal " << static_cast<int>(r);
  }
}

}  // namespace
