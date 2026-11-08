#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

namespace {

TEST(ProgramControlTasksSynth, ExitOutsideAProgramInitialIsStillReported) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic clk;\n"
                           "  logic q;\n"
                           "  always_ff @(posedge clk) begin\n"
                           "    q <= 1'b0;\n"
                           "    $exit();\n"
                           "  end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "system task or system function '$exit' is not synthesizable", 6,
      "5.6.3"));
}

}  // namespace
