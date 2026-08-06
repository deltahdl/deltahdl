#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(SequenceEventSynthesis, InitialWithSequenceEventSkipped) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk, input [7:0] d,\n"
                           "         output logic [7:0] q);\n"
                           "  logic a, b, c;\n"
                           "  sequence abc;\n"
                           "    @(posedge clk) a ##1 b ##1 c;\n"
                           "  endsequence\n"
                           "  always_ff @(posedge clk)\n"
                           "    q <= d;\n"
                           "  initial @(abc) $display(\"matched\");\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
}

}  // namespace
