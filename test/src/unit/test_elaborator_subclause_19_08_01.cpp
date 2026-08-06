#include <gtest/gtest.h>

#include "elaborator/overridden_sample_method.h"

using namespace delta;

namespace {

// §19.8.1: a formal argument of an overridden sample method may only designate
// a coverpoint or a conditional guard expression.
TEST(OverriddenSampleMethod, FormalLegalAsCoverpointOrGuard) {
  EXPECT_TRUE(
      SampleFormalUsageIsLegal(CovergroupNameContext::kCoverpointExpression));
  EXPECT_TRUE(SampleFormalUsageIsLegal(
      CovergroupNameContext::kConditionalGuardExpression));
}

// §19.8.1: a sample formal used as a cross item still designates a coverpoint
// (a bare variable in a cross implicitly creates one), which is why §19.8.1's
// own valid example writes `cross x, a` with a and x as the sample formals.
TEST(OverriddenSampleMethod, FormalLegalAsCrossItem) {
  EXPECT_TRUE(SampleFormalUsageIsLegal(CovergroupNameContext::kCrossList));
}

// §19.8.1: it is an error to use a sample formal argument in any context that
// does not designate a coverpoint or conditional guard — for example the value
// expression of a coverage-option assignment or a bins expression.
TEST(OverriddenSampleMethod, FormalIllegalElsewhere) {
  EXPECT_FALSE(SampleFormalUsageIsLegal(
      CovergroupNameContext::kCoverageOptionAssignment));
  EXPECT_FALSE(
      SampleFormalUsageIsLegal(CovergroupNameContext::kBinsExpression));
  EXPECT_FALSE(SampleFormalUsageIsLegal(CovergroupNameContext::kOther));
}

// §19.8.1: the sample formals are searched before the enclosing scope, so a
// name that matches a sample formal resolves to that formal even when the
// enclosing scope also declares the same name.
TEST(OverriddenSampleMethod, SampleFormalShadowsEnclosingScope) {
  EXPECT_EQ(ResolveCovergroupName(/*name_is_sample_formal=*/true,
                                  /*name_in_enclosing_scope=*/true),
            CovergroupNameResolution::kSampleFormal);
  EXPECT_EQ(ResolveCovergroupName(/*name_is_sample_formal=*/true,
                                  /*name_in_enclosing_scope=*/false),
            CovergroupNameResolution::kSampleFormal);
}

// §19.8.1: a name that is not a sample formal still resolves against the
// enclosing scope, and is unresolved if visible nowhere.
TEST(OverriddenSampleMethod, NonFormalResolvesAgainstEnclosingScope) {
  EXPECT_EQ(ResolveCovergroupName(/*name_is_sample_formal=*/false,
                                  /*name_in_enclosing_scope=*/true),
            CovergroupNameResolution::kEnclosingScope);
  EXPECT_EQ(ResolveCovergroupName(/*name_is_sample_formal=*/false,
                                  /*name_in_enclosing_scope=*/false),
            CovergroupNameResolution::kUnresolved);
}

}  // namespace
