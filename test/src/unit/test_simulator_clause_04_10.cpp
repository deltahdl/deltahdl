#include <gtest/gtest.h>

#include "common/types.h"
#include "simulator/vpi.h"

using namespace delta;

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
  EXPECT_FALSE(IsOneShotPliCallback(kCbValueChange));
}

TEST(PliCallbackTaxonomy, UnknownReasonIsNotOneShot) {
  EXPECT_FALSE(IsOneShotPliCallback(0));
  EXPECT_FALSE(IsOneShotPliCallback(-1));
  EXPECT_FALSE(IsOneShotPliCallback(9999));
}

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
  EXPECT_EQ(RegionForPliCallback(kCbValueChange), Region::kCOUNT);
  EXPECT_EQ(RegionForPliCallback(kCbStmt), Region::kCOUNT);
  EXPECT_EQ(RegionForPliCallback(kCbEndOfSimulation), Region::kCOUNT);
  EXPECT_EQ(RegionForPliCallback(0), Region::kCOUNT);
  EXPECT_EQ(RegionForPliCallback(9999), Region::kCOUNT);
}

TEST(PliCallbackConstants, OneShotCallbackReasonsAreDistinct) {
  EXPECT_NE(kCbAfterDelay, kCbNextSimTime);
  EXPECT_NE(kCbAfterDelay, kCbNBASynch);
  EXPECT_NE(kCbAfterDelay, kCbAtEndOfSimTime);
  EXPECT_NE(kCbNextSimTime, kCbNBASynch);
  EXPECT_NE(kCbNextSimTime, kCbAtEndOfSimTime);
  EXPECT_NE(kCbNBASynch, kCbAtEndOfSimTime);

  EXPECT_NE(kCbAfterDelay, kCbReadWriteSynch);
  EXPECT_NE(kCbAfterDelay, kCbAtStartOfSimTime);
  EXPECT_NE(kCbAfterDelay, kCbReadOnlySynch);
  EXPECT_NE(kCbAfterDelay, kCbValueChange);
}
