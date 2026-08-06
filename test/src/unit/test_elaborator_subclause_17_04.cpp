#include <gtest/gtest.h>

#include "elaborator/checker_context_inference.h"

using namespace delta;

namespace {

TEST(CheckerContextInference, ExplicitlyConnectedFormalUsesItsActual) {
  // §17.4: in the my_check1 instantiation every formal argument is provided
  // explicitly, so each formal keeps its supplied actual and no inference
  // occurs — even when the formal also declares a context value function
  // default.
  EXPECT_EQ(ResolveCheckerArgumentValueSource(
                /*connected_explicitly=*/true,
                /*default_is_context_value_function=*/false),
            CheckerArgumentValueSource::kExplicitActual);
  EXPECT_EQ(ResolveCheckerArgumentValueSource(
                /*connected_explicitly=*/true,
                /*default_is_context_value_function=*/true),
            CheckerArgumentValueSource::kExplicitActual);
}

TEST(CheckerContextInference, OmittedContextValueFormalIsInferredFromContext) {
  // §17.4: in the my_check2 instantiation the optional clock and reset formals
  // are omitted, so each takes its context value function default, which is
  // inferred from the instantiation context.
  EXPECT_EQ(ResolveCheckerArgumentValueSource(
                /*connected_explicitly=*/false,
                /*default_is_context_value_function=*/true),
            CheckerArgumentValueSource::kContextInferredDefault);
}

TEST(CheckerContextInference, OmittedOrdinaryDefaultFormalUsesThatDefault) {
  // §17.4: an omitted optional formal whose default is an ordinary expression
  // rather than a context value function simply uses that default expression.
  EXPECT_EQ(ResolveCheckerArgumentValueSource(
                /*connected_explicitly=*/false,
                /*default_is_context_value_function=*/false),
            CheckerArgumentValueSource::kOrdinaryDefault);
}

TEST(CheckerContextInference, ContextValueDefaultsEvaluatedAtInstantiation) {
  // §17.4: the default values of clock and reset are taken from the
  // instantiation context, not the declaration, so a single checker adapts to
  // each instance.
  EXPECT_EQ(CheckerContextValueDefaultEvaluationSite(),
            ContextValueDefaultEvaluationSite::kInstantiationContext);
}

}  // namespace
