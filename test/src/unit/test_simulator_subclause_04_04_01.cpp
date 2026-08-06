#include <gtest/gtest.h>

#include <array>
#include <cstddef>

#include "common/types.h"

using namespace delta;

// §4.4.1 defines three named groupings over the stratified event scheduler's
// regions: the active region set, the reactive region set, and the iterative
// regions. It also states that every region of a time slot is categorized as
// either a simulation region or a PLI region. These are pure classifications of
// the region model, so they are exercised directly against the production
// predicates in src/common/types.cpp rather than through HDL source.

namespace {

// Every real region, excluding the kCOUNT sentinel.
std::array<Region, kRegionCount> AllRegions() {
  std::array<Region, kRegionCount> regions{};
  for (std::size_t i = 0; i < kRegionCount; ++i) {
    regions[i] = static_cast<Region>(i);
  }
  return regions;
}

// Independent restatement of the §4.4.1 active region set: Active, Inactive,
// Pre-NBA, NBA, Post-NBA.
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

// Independent restatement of the §4.4.1 reactive region set: Reactive,
// Re-Inactive, Pre-Re-NBA, Re-NBA, Post-Re-NBA.
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

// Independent restatement of the fourteen §4.4.1 iterative regions: the active
// and reactive sets, the three Observed regions, and Pre-Postponed. Preponed,
// Pre-Active, and Postponed are deliberately excluded.
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

// The active region set predicate holds for exactly the §4.4.1 members.
TEST(ActiveAndReactiveRegionSetsSim, ActiveRegionSetMembership) {
  for (Region r : AllRegions()) {
    EXPECT_EQ(IsActiveRegionSet(r), ExpectedActive(r))
        << "region ordinal " << static_cast<int>(r);
  }
}

// The reactive region set predicate holds for exactly the §4.4.1 members.
TEST(ActiveAndReactiveRegionSetsSim, ReactiveRegionSetMembership) {
  for (Region r : AllRegions()) {
    EXPECT_EQ(IsReactiveRegionSet(r), ExpectedReactive(r))
        << "region ordinal " << static_cast<int>(r);
  }
}

// The iterative predicate holds for exactly the fourteen §4.4.1 members.
TEST(ActiveAndReactiveRegionSetsSim, IterativeRegionsMembership) {
  for (Region r : AllRegions()) {
    EXPECT_EQ(IsIterativeRegion(r), ExpectedIterative(r))
        << "region ordinal " << static_cast<int>(r);
  }
}

// §4.4.1 lists both the active and reactive region sets among the iterative
// regions, so membership in either set implies an iterative region.
TEST(ActiveAndReactiveRegionSetsSim, ActiveAndReactiveSetsAreIterative) {
  for (Region r : AllRegions()) {
    if (IsActiveRegionSet(r) || IsReactiveRegionSet(r)) {
      EXPECT_TRUE(IsIterativeRegion(r))
          << "region ordinal " << static_cast<int>(r);
    }
  }
}

// The active and reactive region sets are distinct groupings.
TEST(ActiveAndReactiveRegionSetsSim, ActiveAndReactiveSetsAreDisjoint) {
  for (Region r : AllRegions()) {
    EXPECT_FALSE(IsActiveRegionSet(r) && IsReactiveRegionSet(r))
        << "region ordinal " << static_cast<int>(r);
  }
}

// §4.4.1: every event region of a time slot is categorized as a simulation
// region or a PLI region. This checks the categorization is exhaustive; the
// specific membership of each category belongs to §4.4.2/§4.4.3.
TEST(ActiveAndReactiveRegionSetsSim, EveryRegionIsSimulationOrPli) {
  for (Region r : AllRegions()) {
    EXPECT_TRUE(IsSimulationRegion(r) || IsPliRegion(r))
        << "region ordinal " << static_cast<int>(r);
  }
}
