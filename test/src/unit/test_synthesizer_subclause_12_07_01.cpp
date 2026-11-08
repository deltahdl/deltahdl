#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(SequentialLoopSynthesis, UnlowerableStatementIsReportedRatherThanDropped) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, output logic y);\n"
                           "  integer i;\n"
                           "  always_comb begin\n"
                           "    for (i = 0; i < 2; i = i + 1)\n"
                           "      y = a;\n"
                           "  end\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "statement has no lowering in the synthesizer "
                            "and would be dropped from the netlist",
                            4, ""));
}

}  // namespace
