#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(TaggedUnionSynthesis,
     TaggedUnionExpressionIsReportedRatherThanLoweredToZero) {
  SynthFixture f;
  const auto* mod = ElaborateSrc(
      f,
      "module m(input [31:0] a);\n"
      "  typedef union tagged packed { void Invalid; logic [31:0] Valid; } "
      "vint_t;\n"
      "  vint_t u;\n"
      "  assign u = tagged Valid a;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a tagged union expression has no lowering", 4,
                            "11.9"));
}

}  // namespace
