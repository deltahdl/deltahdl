#include <gtest/gtest.h>

#include "elaborator/checker_context_inference.h"
#include "fixture_elaborator.h"

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

TEST(CheckerContextInference, AnInstanceWithAClockToInferIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "checker k(logic v, event clk = $inferred_clock);\n"
      "  a1: assert property (@clk v);\n"
      "endchecker\n"
      "module m;\n"
      "  bit a, clk;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  k u1(a);\n"
      "endmodule\n"
      "module n;\n"
      "  bit a, clk;\n"
      "  always @(posedge clk) begin\n"
      "    k u2(a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
