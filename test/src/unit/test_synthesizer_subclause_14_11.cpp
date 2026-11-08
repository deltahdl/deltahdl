#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(CycleDelaySynthesis, CycleDelayIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk, input din, output reg q);\n"
                           "  logic sample;\n"
                           "  default clocking cb @(posedge clk);\n"
                           "    input sample;\n"
                           "  endclocking\n"
                           "  always begin\n"
                           "    ##3;\n"
                           "    q = din;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cycle delay is not synthesizable", 7, "14.11"));
}

}  // namespace
