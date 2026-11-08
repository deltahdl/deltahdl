#include <gtest/gtest.h>

#include "elaborator/checker_context_inference.h"

using namespace delta;

namespace {

TEST(CheckerContextInference, ExplicitlyConnectedFormalUsesItsActual) {
  EXPECT_EQ(ResolveCheckerArgumentValueSource(true, false),
            CheckerArgumentValueSource::kExplicitActual);
  EXPECT_EQ(ResolveCheckerArgumentValueSource(true, true),
            CheckerArgumentValueSource::kExplicitActual);
}

TEST(CheckerContextInference, OmittedContextValueFormalIsInferredFromContext) {
  EXPECT_EQ(ResolveCheckerArgumentValueSource(false, true),
            CheckerArgumentValueSource::kContextInferredDefault);
}

TEST(CheckerContextInference, OmittedOrdinaryDefaultFormalUsesThatDefault) {
  EXPECT_EQ(ResolveCheckerArgumentValueSource(false, false),
            CheckerArgumentValueSource::kOrdinaryDefault);
}

TEST(CheckerContextInference, ContextValueDefaultsEvaluatedAtInstantiation) {
  EXPECT_EQ(CheckerContextValueDefaultEvaluationSite(),
            ContextValueDefaultEvaluationSite::kInstantiationContext);
}

}  // namespace
