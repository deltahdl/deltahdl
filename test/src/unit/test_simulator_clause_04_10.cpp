#include <gtest/gtest.h>

#include "common/types.h"
#include "simulator/vpi.h"

using namespace delta;

// §4.10 first sentence: PLI callbacks split into two kinds — those that fire
// immediately when activity occurs (e.g. cbValueChange) and those registered
// as a one-shot evaluation event (the callbacks listed in Table 4-1).

TEST(PliCallbackTaxonomy, RegisteredEvaluationCallbacksAreOneShot) {
  EXPECT_TRUE(IsOneShotPliCallback(kCbAfterDelay));
  EXPECT_TRUE(IsOneShotPliCallback(kCbNextSimTime));
  EXPECT_TRUE(IsOneShotPliCallback(kCbReadWriteSynch));
  EXPECT_TRUE(IsOneShotPliCallback(kCbAtStartOfSimTime));
  EXPECT_TRUE(IsOneShotPliCallback(kCbNBASynch));
  EXPECT_TRUE(IsOneShotPliCallback(kCbAtEndOfSimTime));
  EXPECT_TRUE(IsOneShotPliCallback(kCbReadOnlySynch));
}

TEST(PliCallbackTaxonomy, ValueChangeIsImmediate) {
  // cbValueChange fires when the watched object changes — it is the canonical
  // "immediately when some specific activity occurs" case from §4.10.
  EXPECT_FALSE(IsOneShotPliCallback(kCbValueChange));
}

TEST(PliCallbackTaxonomy, UnknownReasonIsNotOneShot) {
  EXPECT_FALSE(IsOneShotPliCallback(0));
  EXPECT_FALSE(IsOneShotPliCallback(-1));
  EXPECT_FALSE(IsOneShotPliCallback(9999));
}

// §4.10 Table 4-1: each row asserts the callback's assigned event region.

TEST(PliCallbackRegion, CbAfterDelayMapsToPreActive) {
  EXPECT_EQ(RegionForPliCallback(kCbAfterDelay), Region::kPreActive);
}

TEST(PliCallbackRegion, CbNextSimTimeMapsToPreActive) {
  EXPECT_EQ(RegionForPliCallback(kCbNextSimTime), Region::kPreActive);
}

TEST(PliCallbackRegion, CbAtStartOfSimTimeMapsToPreActive) {
  EXPECT_EQ(RegionForPliCallback(kCbAtStartOfSimTime), Region::kPreActive);
}

TEST(PliCallbackRegion, CbReadWriteSynchMapsToPreNbaOrPostNba) {
  // Table 4-1 lists "Pre-NBA or Post-NBA" — the implementation may pick either.
  Region r = RegionForPliCallback(kCbReadWriteSynch);
  EXPECT_TRUE(r == Region::kPreNBA || r == Region::kPostNBA)
      << "cbReadWriteSynch must map to Pre-NBA or Post-NBA per Table 4-1";
}

TEST(PliCallbackRegion, CbNbaSynchMapsToPreNba) {
  EXPECT_EQ(RegionForPliCallback(kCbNBASynch), Region::kPreNBA);
}

TEST(PliCallbackRegion, CbAtEndOfSimTimeMapsToPrePostponed) {
  EXPECT_EQ(RegionForPliCallback(kCbAtEndOfSimTime), Region::kPrePostponed);
}

TEST(PliCallbackRegion, CbReadOnlySynchMapsToPostponed) {
  EXPECT_EQ(RegionForPliCallback(kCbReadOnlySynch), Region::kPostponed);
}

TEST(PliCallbackRegion, NonOneShotCallbackHasNoAssignedRegion) {
  // §4.10 only assigns regions to the seven Table 4-1 callbacks. Other
  // reasons (immediately-fired or out-of-table) report no assigned region
  // via the kCOUNT sentinel.
  EXPECT_EQ(RegionForPliCallback(kCbValueChange), Region::kCOUNT);
  EXPECT_EQ(RegionForPliCallback(kCbStmt), Region::kCOUNT);
  EXPECT_EQ(RegionForPliCallback(kCbEndOfSimulation), Region::kCOUNT);
  EXPECT_EQ(RegionForPliCallback(0), Region::kCOUNT);
  EXPECT_EQ(RegionForPliCallback(9999), Region::kCOUNT);
}

// Constants for the four callback reasons named in Table 4-1 but not
// previously defined must exist as distinct values.
TEST(PliCallbackConstants, OneShotCallbackReasonsAreDistinct) {
  EXPECT_NE(kCbAfterDelay, kCbNextSimTime);
  EXPECT_NE(kCbAfterDelay, kCbNBASynch);
  EXPECT_NE(kCbAfterDelay, kCbAtEndOfSimTime);
  EXPECT_NE(kCbNextSimTime, kCbNBASynch);
  EXPECT_NE(kCbNextSimTime, kCbAtEndOfSimTime);
  EXPECT_NE(kCbNBASynch, kCbAtEndOfSimTime);
  // And distinct from the four already-defined reasons.
  EXPECT_NE(kCbAfterDelay, kCbReadWriteSynch);
  EXPECT_NE(kCbAfterDelay, kCbAtStartOfSimTime);
  EXPECT_NE(kCbAfterDelay, kCbReadOnlySynch);
  EXPECT_NE(kCbAfterDelay, kCbValueChange);
}
