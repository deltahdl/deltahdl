#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(FunctionCallSynthesis, FunctionCallIsReportedRatherThanLoweredToZero) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [7:0] d, output logic [7:0] q);\n"
                   "  function logic [7:0] identity(input logic [7:0] v);\n"
                   "    return v;\n"
                   "  endfunction\n"
                   "  assign q = identity(d);\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a function call has no lowering", 5, "13.4"));
}

}  // namespace
