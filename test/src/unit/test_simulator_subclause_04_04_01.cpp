#include <gtest/gtest.h>

#include <array>
#include <cstddef>

#include "common/types.h"

using namespace delta;

namespace {

std::array<Region, kRegionCount> AllRegions() {
  std::array<Region, kRegionCount> regions{};
  for (std::size_t i = 0; i < kRegionCount; ++i) {
    regions[i] = static_cast<Region>(i);
  }
  return regions;
}

bool ExpectedActive(Region r) {
  switch (r) {
    case Region::kActive:
    case Region::kInactive:
    case Region::kPreNBA:
    case Region::kNBA:
    case Region::kPostNBA:
      return true;
    default:
      return false;
  }
}

bool ExpectedReactive(Region r) {
  switch (r) {
    case Region::kReactive:
    case Region::kReInactive:
    case Region::kPreReNBA:
    case Region::kReNBA:
    case Region::kPostReNBA:
      return true;
    default:
      return false;
  }
}

bool ExpectedIterative(Region r) {
  switch (r) {
    case Region::kActive:
    case Region::kInactive:
    case Region::kPreNBA:
    case Region::kNBA:
    case Region::kPostNBA:
    case Region::kPreObserved:
    case Region::kObserved:
    case Region::kPostObserved:
    case Region::kReactive:
    case Region::kReInactive:
    case Region::kPreReNBA:
    case Region::kReNBA:
    case Region::kPostReNBA:
    case Region::kPrePostponed:
      return true;
    default:
      return false;
  }
}

}  // namespace

TEST(ActiveAndReactiveRegionSetsSim, ActiveRegionSetMembership) {
  for (Region r : AllRegions()) {
    EXPECT_EQ(IsActiveRegionSet(r), ExpectedActive(r))
        << "region ordinal " << static_cast<int>(r);
  }
}

TEST(ActiveAndReactiveRegionSetsSim, ReactiveRegionSetMembership) {
  for (Region r : AllRegions()) {
    EXPECT_EQ(IsReactiveRegionSet(r), ExpectedReactive(r))
        << "region ordinal " << static_cast<int>(r);
  }
}

TEST(ActiveAndReactiveRegionSetsSim, IterativeRegionsMembership) {
  for (Region r : AllRegions()) {
    EXPECT_EQ(IsIterativeRegion(r), ExpectedIterative(r))
        << "region ordinal " << static_cast<int>(r);
  }
}

TEST(ActiveAndReactiveRegionSetsSim, ActiveAndReactiveSetsAreIterative) {
  for (Region r : AllRegions()) {
    if (IsActiveRegionSet(r) || IsReactiveRegionSet(r)) {
      EXPECT_TRUE(IsIterativeRegion(r))
          << "region ordinal " << static_cast<int>(r);
    }
  }
}

TEST(ActiveAndReactiveRegionSetsSim, ActiveAndReactiveSetsAreDisjoint) {
  for (Region r : AllRegions()) {
    EXPECT_FALSE(IsActiveRegionSet(r) && IsReactiveRegionSet(r))
        << "region ordinal " << static_cast<int>(r);
  }
}

TEST(ActiveAndReactiveRegionSetsSim, EveryRegionIsSimulationOrPli) {
  for (Region r : AllRegions()) {
    EXPECT_TRUE(IsSimulationRegion(r) || IsPliRegion(r))
        << "region ordinal " << static_cast<int>(r);
  }
}
