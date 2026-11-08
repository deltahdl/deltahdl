#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(SequenceSynthesis, MultipleSequenceFormsCoexistInSynth) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input clk, input d, output logic q);\n"
                           "  sequence s_concat;\n"
                           "    @(posedge clk) d ##1 d;\n"
                           "  endsequence\n"
                           "  sequence s_range;\n"
                           "    @(posedge clk) d ##[1:3] d;\n"
                           "  endsequence\n"
                           "  sequence s_rep;\n"
                           "    @(posedge clk) d[*2];\n"
                           "  endsequence\n"
                           "  always_ff @(posedge clk)\n"
                           "    q <= d;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(aig->outputs.empty());
}

}  // namespace
