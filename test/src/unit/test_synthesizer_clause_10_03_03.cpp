#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(ContAssignDelaySynth, SingleDelayIgnoredInSynthesis) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, output y);\n"
                           "  assign #10 y = a;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 1);
  EXPECT_EQ(aig->outputs.size(), 1);
  EXPECT_EQ(aig->outputs[0], AigLit(aig->inputs[0], false));
}

TEST(ContAssignDelaySynth, RiseFallDelayIgnoredInSynthesis) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, output y);\n"
                           "  assign #(5, 10) y = a;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 1);
  EXPECT_EQ(aig->outputs.size(), 1);
  EXPECT_EQ(aig->outputs[0], AigLit(aig->inputs[0], false));
}

TEST(ContAssignDelaySynth, ThreeDelayIgnoredInSynthesis) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(input a, output y);\n"
                           "  assign #(5, 10, 15) y = a;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 1);
  EXPECT_EQ(aig->outputs.size(), 1);
  EXPECT_EQ(aig->outputs[0], AigLit(aig->inputs[0], false));
}

TEST(ContAssignDelaySynth, DelayConstantProducesCorrectValue) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m(output y);\n"
                           "  assign #10 y = 1'b1;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs[0], AigGraph::kConstTrue);
}

}  // namespace
