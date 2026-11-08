#include <gtest/gtest.h>

#include "elaborator/overridden_sample_method.h"

using namespace delta;

namespace {

TEST(OverriddenSampleMethod, FormalLegalAsCoverpointOrGuard) {
  EXPECT_TRUE(
      SampleFormalUsageIsLegal(CovergroupNameContext::kCoverpointExpression));
  EXPECT_TRUE(SampleFormalUsageIsLegal(
      CovergroupNameContext::kConditionalGuardExpression));
}

TEST(OverriddenSampleMethod, FormalLegalAsCrossItem) {
  EXPECT_TRUE(SampleFormalUsageIsLegal(CovergroupNameContext::kCrossList));
}

TEST(OverriddenSampleMethod, FormalIllegalElsewhere) {
  EXPECT_FALSE(SampleFormalUsageIsLegal(
      CovergroupNameContext::kCoverageOptionAssignment));
  EXPECT_FALSE(
      SampleFormalUsageIsLegal(CovergroupNameContext::kBinsExpression));
  EXPECT_FALSE(SampleFormalUsageIsLegal(CovergroupNameContext::kOther));
}

TEST(OverriddenSampleMethod, SampleFormalShadowsEnclosingScope) {
  EXPECT_EQ(ResolveCovergroupName(true, true),
            CovergroupNameResolution::kSampleFormal);
  EXPECT_EQ(ResolveCovergroupName(true, false),
            CovergroupNameResolution::kSampleFormal);
}

TEST(OverriddenSampleMethod, NonFormalResolvesAgainstEnclosingScope) {
  EXPECT_EQ(ResolveCovergroupName(false, true),
            CovergroupNameResolution::kEnclosingScope);
  EXPECT_EQ(ResolveCovergroupName(false, false),
            CovergroupNameResolution::kUnresolved);
}

}  // namespace
